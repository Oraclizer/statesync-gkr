//! Public inputs and circuit-witness generation.

use ssgkr_primitives::field::{BaseField, PrimeCharacteristicRing};
use ssgkr_primitives::hash::{DefaultHasher, Digest, HashGadget, leaf_fold};

use crate::compile::InputLayout;
use crate::params::{LayerStrategy, SmtParams};
use crate::smt::{AssetId, LeafState, SmtError, SmtOpKind, SmtOperation, SmtWitness};
use ssgkr_protocol::{CircuitWitness, LayeredCircuit, evaluate_circuit};

// Named imports on purpose (the prelude glob would shadow the std derives
// and `vec!` - see the note in ssgkr-primitives::hash).
#[cfg(creusot)]
use creusot_std::prelude::{ensures, requires};

/// Creusot specifications absent from creusot-std at the pinned rev:
///
/// - `Result::map_err`: same shape as the `Result::map` spec in
///   compile.rs (`Ok`/`Err` preservation plus the closure's
///   postcondition - the plain std behavior).
/// - (R2 update) the R1 claim-free extern spec for
///   `ssgkr_protocol::circuit::evaluate_circuit` is GONE: the protocol
///   crate is itself Creusot-verified since R2, and Creusot rejects
///   extern specs targeting items of verified crates. `evaluate_circuit`
///   now carries its admissibility directly (a `#[trusted]` marker at
///   its definition - the iterator-spec wall, see the protocol crate).
#[cfg(creusot)]
mod creusot_specs {
    use creusot_std::prelude::*;

    extern_spec! {
        impl<T, E> Result<T, E> {
            #[requires(match self { Ok(_) => true, Err(e) => op.precondition((e,)) })]
            #[ensures(match self {
                Ok(t) => resolve(op) && result == Ok(t),
                Err(e) => exists<r> result == Err(r) && op.postcondition_once((e,), r),
            })]
            fn map_err<F, O: FnOnce(E) -> F>(self, op: O) -> Result<T, F> {
                match self {
                    Ok(t) => Ok(t),
                    Err(e) => Err(op(e)),
                }
            }
        }
    }
}

/// Public inputs of one proved operation.
///
/// SEAL[S-6]: field set AND order are frozen at G1. Everything the
/// verifier must trust externally goes here and ONLY here; the transcript
/// absorbs these fields in declaration order (S-5). Must stay in sync
/// with the public-input convention noted at the end of
/// `formal/isabelle/SMT_Circuit_Compiler_Correctness/Compiler_Correctness.thy`.
///
/// (Under `--cfg creusot` the verifier's `PartialEq` derive needs a
/// `DeepModel`; every field has one - digests via the black-box boundary
/// impl - so it is simply derived. Attribute-only, no S-6 change.)
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(creusot, derive(creusot_std::prelude::DeepModel))]
pub struct PublicInputs {
    /// Root before the operation.
    pub old_root: Digest<BaseField>,
    /// Root after the operation (= `old_root` for read-only ops).
    pub new_root: Digest<BaseField>,
    /// Operation kind tag (fixed encoding: 0 = Membership,
    /// 1 = NonMembership, 2 = Update).
    pub op_kind_tag: u8,
    /// Asset key.
    pub asset_id: AssetId,
    /// Digest binding the operation's value payload. Frozen per-op
    /// mapping (S-6): Membership = leaf pre-hash of the asserted
    /// occupied leaf; Update = leaf pre-hash of the NEW leaf state;
    /// NonMembership = leaf pre-hash of the asserted Empty/Tombstone
    /// state. Always `h_leaf(LeafState::encode(..))`.
    pub value_digest: Digest<BaseField>,
}

impl PublicInputs {
    /// Tag for an operation kind (frozen encoding).
    ///
    /// R1 refinement anchor (Creusot-checked): the tag-lane value map of
    /// `Cmp_Model`'s public-input convention, pinned literally (u8 values
    /// are machine-transparent; no opaque field constructor involved).
    #[cfg_attr(creusot, ensures(result@ == match kind {
        SmtOpKind::Membership => 0,
        SmtOpKind::NonMembership => 1,
        SmtOpKind::Update => 2,
    }))]
    pub fn kind_tag(kind: SmtOpKind) -> u8 {
        match kind {
            SmtOpKind::Membership => 0,
            SmtOpKind::NonMembership => 1,
            SmtOpKind::Update => 2,
        }
    }
}

/// The running Merkle accumulators `acc_0..acc_d` along one path: `acc_0` is
/// the leaf pre-hash, `acc_{l+1}` compresses `acc_l` with sibling `l` in the
/// key-bit order (exactly `MerklePath::compute_root`'s recursion, retaining
/// the intermediates the circuit checks per level). Errs when the leaf
/// encoding violates the structural bound (`leaf_max_fields`).
fn acc_chain(
    hasher: &DefaultHasher,
    key: AssetId,
    leaf: &LeafState,
    siblings: &[Digest<BaseField>],
) -> Result<Vec<Digest<BaseField>>, SmtError> {
    let mut chain = Vec::with_capacity(siblings.len() + 1);
    let mut acc = hasher.hash_leaf(&leaf.encode())?;
    chain.push(acc);
    let mut bits = key.0;
    for sib in siblings {
        acc = if bits & 1 == 0 {
            hasher.compress(&acc, sib)
        } else {
            hasher.compress(sib, &acc)
        };
        chain.push(acc);
        bits >>= 1;
    }
    Ok(chain)
}

/// Copy an 8-lane digest into the input vector at `base`.
fn put_digest(inputs: &mut [BaseField], base: u32, d: &Digest<BaseField>) {
    for (i, &v) in d.0.iter().enumerate() {
        inputs[base as usize + i] = v;
    }
}

/// The operation's asset key.
fn op_key(op: &SmtOperation) -> AssetId {
    match op {
        SmtOperation::Membership { key, .. }
        | SmtOperation::NonMembership { key }
        | SmtOperation::Update { key, .. } => *key,
    }
}

/// Generate the circuit witness (all wire assignments) for one operation.
///
/// Split from [`crate::compile`] on purpose: circuit STRUCTURE is
/// witness-independent and cached per (kind, params, strategy); only this
/// function runs per proved operation (Module 3 batching premise). It builds
/// the input vector (leaf pre-image fold, the accumulator chain(s), siblings,
/// key bits, public roots and value digest) using the production
/// [`DefaultHasher`] (Poseidon2), then evaluates the circuit - so the witness
/// matches the circuit by construction.
///
/// FV-CONTRACT (Creusot, R1 #10 - the Rust-level Theorem A target).
/// This REPLACES an earlier ungated `is_accepting(evaluate_circuit(
/// compile(..), ..)) <=> smt_valid_native(..)` sketch, which was FALSE:
/// for read-only operations the input vector has no `new_root` slot
/// (the layout binds ONE root), so the circuit cannot see
/// `new_root != old_root` while `smt_valid_native` checks
/// `new_root == old_root` - a valid witness plus unequal public roots
/// makes the circuit side true and the native side false. The model
/// closes exactly this gap with the `pub_ok` gate, so the target is the
/// GATED, existentially quantified `theorem_A_compilation_soundness`
/// (`Compiler_Correctness.thy`):
///
///   (exists vd w. verifier_accept op root root' vd w)
///     <-> (exists w. smt_valid op root root' w)
///
///   verifier_accept op root root' vd w <->
///        pub_ok op root root' vd    -- facade public-input checks:
///                                   --   kind_of op /= KUpdate ==> root' = root
///                                   --   op_key op < 2 ^ depth
///                                   --   vd_ok: vd canonical per kind
///                                   --     (Membership: h_leaf (Occupied v);
///                                   --      NonMembership: h_leaf Empty or
///                                   --      h_leaf Tombstone; Update: h_leaf new)
///     /\ length (snd w) = depth     -- path-length guard (THIS function's
///                                   --   machine-checked slice, via
///                                   --   build_input_vector's Ok-necessity)
///     /\ echo_ok op w               -- witness echoes: NonMembership:
///                                   --   fst w in {Empty, Tombstone};
///                                   --   Update: fst w = old
///     /\ circuit_accept (compile (kind_of op))
///                       (encode_witness op root root' vd w)
///
/// Placement across the Rust surface: the `pub_ok`/`echo_ok` gates are
/// the facade's public-input checks (`verify_sync_op`, R3 scope);
/// `circuit_accept` is `is_accepting`/`evaluate_circuit` (protocol
/// crate, R2 scope); THIS function owns the canonical witness encoding
/// (`encode_witness`) and the path-length guard. No bare per-witness
/// equivalence is claimable at any single function.
///
/// Tool status: `evaluate_circuit`/`map_err` now carry claim-free
/// admissibility specs (see `creusot_specs`), and the trap-13 codegen
/// boundary on [`build_input_vector`]'s layout consumption is worked
/// around by the opaque-projection seam (compile.rs). THIS function is
/// Creusot-green with the machine-width `requires` below - a safety and
/// call-admissibility result with ZERO semantic claims (no ensures):
/// the semantic slice waits on `build_input_vector`'s monolithic-VC
/// wall (see there), so no witness-chain meaning is asserted yet.
#[cfg_attr(creusot, requires(params.depth@ <= 0xFFFF && params.leaf_max_fields@ <= 0xFFFF))]
#[cfg_attr(creusot, requires(circuit.input_width_bits@ < 64))]
pub fn generate_witness(
    params: &SmtParams,
    _strategy: LayerStrategy,
    circuit: &LayeredCircuit<BaseField>,
    op: &SmtOperation,
    public_inputs: &PublicInputs,
    witness: &SmtWitness,
) -> Result<CircuitWitness<BaseField>, SmtError> {
    let inputs = build_input_vector(params, circuit.input_width_bits, op, public_inputs, witness)?;
    evaluate_circuit(circuit, &inputs).map_err(|_| SmtError::PathLengthMismatch {
        expected: 1usize << circuit.input_width_bits,
        found: inputs.len(),
    })
}

/// Build the circuit input vector for one operation (leaf pre-image fold,
/// accumulator chain(s) via [`DefaultHasher`], siblings, key bits, public roots
/// and value digest), padded to `2^input_width_bits`.
///
/// This is the light part of proving: the verifier reuses it to reconstruct
/// the input MLE and discharge the residual input claim (internal-verifier
/// model, seal S-4) WITHOUT re-evaluating the whole circuit.
///
/// FV-CONTRACT (Creusot, R1 - designed; the Ok-necessity slice below is
/// the target, body VCs still open - see the tool boundary note):
///   #[requires(params.depth@ <= 0xFFFF && params.leaf_max_fields@ <= 0xFFFF)]
///   #[requires(input_width_bits@ < 64)]
///   #[ensures(match result {
///       Ok(_) => witness.path.siblings@.len() == params.depth@,
///       Err(_) => true,       // ~ the path_ok length guard, as in compute_root
///   })]
///
/// Tool boundary history (Creusot 0.13.0-dev rev 7af97e00):
/// - RESOLVED (this session): consuming `InputLayout::new`'s contract
///   from outside compile.rs used to break codegen (literal
///   `ERROR_UNBOUND_*` tokens in this module's coma - trap 13, upstream
///   report drafted). The layout contracts are now routed through opaque
///   `#[logic]` projections (compile.rs), and this module's coma
///   generates VALID why3 again (0 tokens, the prover actually runs).
/// - REMAINING: `vc_build_input_vector` fails as ONE monolithic goal
///   (47/48 theory goals prove, the root vc does not split - no `-X`
///   subgoal detail, `proof.json` records a single null), the signature
///   of the foreign-element `Vec<BaseField>` direct-mutation
///   invariant-threading wall documented on `leaf_fold` (hash.rs): this
///   body fills `vec![ZERO; 1 << bits]` by indexed writes exactly the
///   same way. Rev-needed together with `leaf_fold`'s ensures; the
///   designed ensures above stays carried (doc-only) until the wall
///   lifts - an ACTIVE unproved ensures would be assumed by callers,
///   which is exactly the modular-verification lie this development
///   refuses. The `requires` are active (impositions, not claims).
#[cfg_attr(creusot, requires(params.depth@ <= 0xFFFF && params.leaf_max_fields@ <= 0xFFFF))]
#[cfg_attr(creusot, requires(input_width_bits@ < 64))]
pub fn build_input_vector(
    params: &SmtParams,
    input_width_bits: usize,
    op: &SmtOperation,
    public_inputs: &PublicInputs,
    witness: &SmtWitness,
) -> Result<Vec<BaseField>, SmtError> {
    let depth = params.depth as usize;
    let siblings = &witness.path.siblings;
    if siblings.len() != depth {
        return Err(SmtError::PathLengthMismatch {
            expected: depth,
            found: siblings.len(),
        });
    }
    let leaf_max = params.leaf_max_fields as usize;
    let hasher = DefaultHasher::new(leaf_max);
    let layout = InputLayout::new(op.kind(), depth, leaf_max);
    let key = op_key(op);

    let mut inputs = vec![BaseField::ZERO; 1usize << input_width_bits];

    // Primary leaf: the authenticated leaf (for Update, the OLD leaf).
    let primary_leaf = match op {
        SmtOperation::Update { old_leaf, .. } => old_leaf,
        _ => &witness.leaf,
    };

    for (j, v) in leaf_fold(&primary_leaf.encode(), leaf_max)?
        .into_iter()
        .enumerate()
    {
        inputs[layout.leaf_pre() as usize + j] = v;
    }
    let chain = acc_chain(&hasher, key, primary_leaf, siblings)?;
    for (l, acc) in chain.iter().enumerate() {
        put_digest(&mut inputs, layout.acc(l), acc);
    }
    for (l, sib) in siblings.iter().enumerate() {
        put_digest(&mut inputs, layout.sib(l), sib);
        let bit = (key.0 >> l) & 1;
        inputs[layout.key_bit(l) as usize] = BaseField::from_u32(bit as u32);
    }
    put_digest(&mut inputs, layout.root(), &public_inputs.old_root);
    put_digest(
        &mut inputs,
        layout.value_digest(),
        &public_inputs.value_digest,
    );

    if let SmtOperation::Update { new_leaf, .. } = op {
        for (j, v) in leaf_fold(&new_leaf.encode(), leaf_max)?
            .into_iter()
            .enumerate()
        {
            inputs[layout.leaf_pre2() as usize + j] = v;
        }
        let chain2 = acc_chain(&hasher, key, new_leaf, siblings)?;
        for (l, acc) in chain2.iter().enumerate() {
            put_digest(&mut inputs, layout.acc2(l), acc);
        }
        put_digest(&mut inputs, layout.root2(), &public_inputs.new_root);
    }

    Ok(inputs)
}
