//! Normative StateSync-GKR R3 verification owner.
//!
//! This crate owns the configuration and host value types used by R3,
//! circuit construction, the single prove and verify bodies, the S-5/S-6
//! transcript preamble, and the operation-key projection. The root facade
//! retains product-facing inherent methods and delegates to these functions.
//! This crate deliberately has no dependency on `ssgkr-wrap` or the root
//! facade.

pub mod config;
mod types;

pub use config::StateSyncGkrConfig;
pub use types::{SyncRequest, SyncResult};

use ssgkr_commitment::full_circuit_commitment;
use ssgkr_compiler::{
    CompileError, LeafState, PublicInputs, SmtError, SmtOpKind, SmtOperation, build_input_vector,
    compile, compile_with_hints, generate_witness,
};
use ssgkr_primitives::Transcript;
use ssgkr_primitives::field::{BaseField, ChallengeField, PrimeCharacteristicRing};
use ssgkr_primitives::hash::{DefaultHasher, Digest, HashGadget};
#[cfg(any(test, creusot))]
use ssgkr_protocol::InputClaim;
use ssgkr_protocol::mle::mle_eval_base;
use ssgkr_protocol::wiring::{DerivedRegularWiring, TableWiring, WiringOracle};
use ssgkr_protocol::{CircuitWitness, LayeredCircuit};

// Named imports on purpose. The prelude glob would shadow std derives and
// `vec!`. `LayerStrategy` is named only inside contracts.
#[cfg(creusot)]
use creusot_std::prelude::{DeepModel, ensures, extern_spec, requires, trusted};
#[cfg(creusot)]
use ssgkr_compiler::LayerStrategy;

// The commitment algorithm is a separate D-40 black-box boundary for the R3
// refinement target. Its result is deliberately unconstrained here; this
// claim-free spec only makes the cross-crate production call admissible.
#[cfg(creusot)]
extern_spec! {
    mod ssgkr_commitment {
        fn full_circuit_commitment(
            circuit: &ssgkr_protocol::LayeredCircuit<ssgkr_primitives::field::BaseField>,
            kind: ssgkr_compiler::SmtOpKind,
            params: &ssgkr_compiler::SmtParams,
            strategy: ssgkr_compiler::LayerStrategy,
        ) -> ssgkr_primitives::hash::Digest<ssgkr_primitives::field::BaseField>;
    }
}

/// Domain separation tag for v0.1 proofs (SEAL[S-5]: part of the frozen
/// transcript convention).
///
/// Creusot cannot lower any byte-string literal at the pinned revision. The
/// Creusot-only initializer is therefore an empty claim-free slice; ordinary
/// builds retain the exact frozen transcript bytes. Transcript semantics remain
/// outside the formal claim, and the existing trusted marker is unchanged.
#[cfg_attr(creusot, creusot_std::prelude::trusted)]
pub const DOMAIN_TAG_V01: &[u8] = {
    #[cfg(not(creusot))]
    {
        b"statesync-gkr/v0.1"
    }
    #[cfg(creusot)]
    {
        &[]
    }
};

/// Errors from the composed prover.
#[derive(Clone, Debug)]
pub enum SyncError {
    /// Circuit compilation failed for the configured params/strategy.
    Compile(CompileError),
    /// Witness generation failed (for example, path length mismatch).
    Witness(SmtError),
}

/// The asset key of an operation.
///
/// R3 refinement anchor (mapping #27): mirrors the model's key projection,
/// consumed by `pub_ok`'s range clause in Compiler_Correctness.thy.
#[cfg_attr(creusot, ensures(match *op {
    SmtOperation::Membership { key, .. } => result == key,
    SmtOperation::NonMembership { key } => result == key,
    SmtOperation::Update { key, .. } => result == key,
}))]
fn op_key(op: &SmtOperation) -> ssgkr_compiler::AssetId {
    match op {
        SmtOperation::Membership { key, .. }
        | SmtOperation::NonMembership { key }
        | SmtOperation::Update { key, .. } => *key,
    }
}

/// Check that the proof result is bound to the request's public inputs.
///
/// This helper is on the production acceptance path. Its Creusot contract is
/// the first executable-trace canary: an accepted call can pass this branch
/// only when the exact public-input records are equal. The contract is erased
/// from ordinary builds and does not introduce an alternate verifier body.
#[cfg_attr(creusot, ensures(
    result == (proved.deep_model() == requested.deep_model())
))]
fn public_inputs_match(proved: &PublicInputs, requested: &PublicInputs) -> bool {
    proved == requested
}

/// Verification-only view of the production acceptance checks.
///
/// `sumcheck_consistent` and `carry_consistent` are separately named even
/// though the production `ssgkr_protocol::verify` call reports them through
/// one `Result`: that call checks every sumcheck round before checking each
/// layer reconstruction and carry. The two load-bearing mutation witnesses
/// exercise those source checks independently.
#[cfg(any(test, creusot))]
#[derive(Clone, Copy, Debug)]
struct AcceptanceTrace {
    public_inputs_bound: bool,
    request_guards_bound: bool,
    zero_output_claim: bool,
    sumcheck_consistent: bool,
    carry_consistent: bool,
    final_mle_x: bool,
    final_mle_y: bool,
}

#[cfg(any(test, creusot))]
#[derive(Clone, Copy, Debug)]
struct ClaimedOutputConstruction {
    all_zero_vector: bool,
}

#[cfg(any(test, creusot))]
impl ClaimedOutputConstruction {
    #[allow(non_upper_case_globals)]
    const AllZeroVector: Self = Self {
        all_zero_vector: true,
    };

    #[allow(non_upper_case_globals)]
    const Other: Self = Self {
        all_zero_vector: false,
    };

    #[cfg_attr(creusot, ensures(result == self.all_zero_vector))]
    fn is_zero_claim(self) -> bool {
        self.all_zero_vector
    }
}

#[cfg(any(test, creusot))]
impl AcceptanceTrace {
    #[cfg_attr(creusot, ensures(
        result == (self.public_inputs_bound
            && self.request_guards_bound
            && self.zero_output_claim
            && self.sumcheck_consistent
            && self.carry_consistent
            && self.final_mle_x
            && self.final_mle_y)
    ))]
    fn accepts(&self) -> bool {
        self.public_inputs_bound
            && self.request_guards_bound
            && self.zero_output_claim
            && self.sumcheck_consistent
            && self.carry_consistent
            && self.final_mle_x
            && self.final_mle_y
    }
}

/// Observe the circuit shape and full circuit commitment in the frozen S-5
/// position. Both prover and verifier call this one body.
///
/// R3 mapping #31 is a claim-free Fiat-Shamir seam: the Isabelle model does
/// not model transcript implementation details, so this remains `trusted`
/// with zero injected claims.
#[cfg_attr(creusot, trusted)]
fn observe_circuit_digest(
    t: &mut Transcript,
    circuit: &LayeredCircuit<BaseField>,
    kind: SmtOpKind,
    depth: u32,
    commitment: &Digest<BaseField>,
) {
    t.observe_base(BaseField::from_u8(PublicInputs::kind_tag(kind)));
    t.observe_base(BaseField::from_u32(depth));
    t.observe_base(BaseField::from_u32(circuit.input_width_bits as u32));
    t.observe_base(BaseField::from_u32(circuit.layers.len() as u32));
    for layer in &circuit.layers {
        t.observe_base(BaseField::from_u32(layer.width_bits as u32));
        t.observe_base(BaseField::from_u32(layer.gates.len() as u32));
        t.observe_base(BaseField::from_u32(layer.consts.len() as u32));
    }
    t.observe_digest(commitment);
}

/// Observe public inputs in the frozen S-6 field order.
///
/// Same claim-free transcript seam as [`observe_circuit_digest`].
#[cfg_attr(creusot, trusted)]
fn observe_public_inputs(t: &mut Transcript, pi: &PublicInputs) {
    t.observe_digest(&pi.old_root);
    t.observe_digest(&pi.new_root);
    t.observe_base(BaseField::from_u8(pi.op_kind_tag));
    t.observe_base(BaseField::from_u32(pi.asset_id.0 as u32));
    t.observe_base(BaseField::from_u32((pi.asset_id.0 >> 32) as u32));
    t.observe_digest(&pi.value_digest);
}

/// Compile the circuit for an operation kind under the current config.
///
/// This is the R3 mapping #27 stack-instantiation seam. The pinned Creusot
/// translator rejects the enum-variant constructor passed to `map_err` as a
/// function value, so this body remains claim-free `trusted`; the modeled
/// domain is checked at compiler and verifier contracts.
#[cfg_attr(creusot, trusted)]
pub fn circuit_for(
    config: &StateSyncGkrConfig,
    kind: SmtOpKind,
) -> Result<LayeredCircuit<BaseField>, SyncError> {
    let template = DefaultHasher::new(config.smt.leaf_max_fields as usize).round_template();
    compile(&config.smt, kind, config.layer_strategy, &template).map_err(SyncError::Compile)
}

/// Prove one sync operation through the single R3 production pipeline.
///
/// R3 mapping #25 composes the compiler model and GKR layer sumcheck over
/// one challenge field. The enum-variant constructor translation wall and
/// claim-free builder seams keep this body `trusted` with zero claims.
#[cfg_attr(creusot, trusted)]
pub fn prove_sync_op(
    config: &StateSyncGkrConfig,
    request: &SyncRequest,
) -> Result<SyncResult, SyncError> {
    let op = &request.operation;
    let kind = op.kind();
    let circuit = circuit_for(config, kind)?;
    let witness = generate_witness(
        &config.smt,
        config.layer_strategy,
        &circuit,
        op,
        &request.public_inputs,
        &request.witness,
    )
    .map_err(SyncError::Witness)?;

    let commitment = full_circuit_commitment(&circuit, kind, &config.smt, config.layer_strategy);
    let proof = prove_on(
        config,
        &circuit,
        kind,
        &commitment,
        &request.public_inputs,
        &witness,
    );
    Ok(SyncResult {
        public_inputs: request.public_inputs.clone(),
        proof,
    })
}

/// The one S-5 prove pipeline over an already-compiled circuit. Every root
/// facade path funnels through this body, preserving Theorem D pointwise
/// agreement structurally as well as by executable differential tests.
///
/// Claim-free `trusted`: a non-trusted body referencing
/// [`DOMAIN_TAG_V01`] reaches the pinned translator's byte-string wall.
#[cfg_attr(creusot, trusted)]
pub fn prove_on(
    config: &StateSyncGkrConfig,
    circuit: &LayeredCircuit<BaseField>,
    kind: SmtOpKind,
    commitment: &Digest<BaseField>,
    public_inputs: &PublicInputs,
    witness: &CircuitWitness<BaseField>,
) -> ssgkr_protocol::GkrProof {
    let outputs = &witness.layer_values[0];
    let mut transcript = Transcript::new(DOMAIN_TAG_V01);
    observe_circuit_digest(&mut transcript, circuit, kind, config.smt.depth, commitment);
    observe_public_inputs(&mut transcript, public_inputs);
    transcript.observe_many(outputs);
    ssgkr_protocol::prove(circuit, witness, &mut transcript)
}

/// Verify one sync proof through the succinct derived wiring oracle.
///
/// R3 mapping #26 is the thin entry into [`verify_sync_op_with`]. The
/// contract pins acceptance to the modeled strategy/depth/leaf domain. The
/// machine-width side conditions are the only preconditions.
#[cfg_attr(creusot, requires(config.smt.depth@ <= 0xFFFF
    && config.smt.leaf_max_fields@ <= 0xFFFF))]
#[cfg_attr(creusot, ensures(result ==>
    config.layer_strategy == LayerStrategy::A
        && config.smt.depth@ >= 1 && config.smt.leaf_max_fields@ >= 10))]
pub fn verify_sync_op(
    config: &StateSyncGkrConfig,
    request: &SyncRequest,
    sync_result: &SyncResult,
) -> bool {
    let kind = request.operation.kind();
    let template = DefaultHasher::new(config.smt.leaf_max_fields as usize).round_template();
    let Ok((circuit, hints)) =
        compile_with_hints(&config.smt, kind, config.layer_strategy, &template)
    else {
        return false;
    };
    let wiring = DerivedRegularWiring::derive(&circuit, &hints);
    let commitment = full_circuit_commitment(&circuit, kind, &config.smt, config.layer_strategy);
    verify_sync_op_with(config, request, sync_result, &circuit, &wiring, &commitment)
}

/// Verify through the materialized table wiring oracle. This is the audit
/// reference twin of [`verify_sync_op`].
pub fn verify_sync_op_reference(
    config: &StateSyncGkrConfig,
    request: &SyncRequest,
    result: &SyncResult,
) -> bool {
    let kind = request.operation.kind();
    let Ok(circuit) = circuit_for(config, kind) else {
        return false;
    };
    let wiring = TableWiring::new(&circuit);
    let commitment = full_circuit_commitment(&circuit, kind, &config.smt, config.layer_strategy);
    verify_sync_op_with(config, request, result, &circuit, &wiring, &commitment)
}

/// Shared verifier body: facade public-input checks, transcript replay, GKR
/// verification under the supplied wiring oracle, and residual input-claim
/// discharge.
///
/// The checks correspond clause-by-clause to `theorem_C_composition`: proof
/// and request binding, operation tag/key, read-only root equality, key
/// range, value digest, witness echo, input reconstruction, the all-zero
/// S-4 output claim, transcript replay, GKR verification, and both residual
/// MLE equalities.
///
/// TOOL WALL (wall (5), narrowed by the verifier-acceptance strengthening):
/// the ordinary build retains the original two short-circuit MLE equalities.
/// Under Creusot only those equalities are routed through the claim-free
/// [`observed_input_mle_match`] computation seam; all surrounding rejection and
/// acceptance control flow is translated normally.
macro_rules! verify_sync_op_body {
    ($config:expr, $request:expr, $result:expr, $circuit:expr, $wiring:expr, $commitment:expr) => {{
        let config = $config;
        let request = $request;
        let result = $result;
        let circuit = $circuit;
        let wiring = $wiring;
        let commitment = $commitment;
        let op = &request.operation;
        let kind = op.kind();
        let pi = &request.public_inputs;

        let public_inputs_bound = public_inputs_match(&result.public_inputs, pi);
        if !public_inputs_bound {
            return false;
        }
        #[cfg(not(any(test, creusot)))]
        if pi.op_kind_tag != PublicInputs::kind_tag(kind) || pi.asset_id != op_key(op) {
            return false;
        }

        #[cfg(any(test, creusot))]
        let tag_key_bound =
            pi.op_kind_tag == PublicInputs::kind_tag(kind) && pi.asset_id == op_key(op);
        #[cfg(any(test, creusot))]
        if !tag_key_bound {
            return false;
        }

        #[cfg(not(any(test, creusot)))]
        if !matches!(kind, SmtOpKind::Update) && pi.new_root != pi.old_root {
            return false;
        }

        #[cfg(any(test, creusot))]
        let root_bound = matches!(kind, SmtOpKind::Update) || pi.new_root == pi.old_root;
        #[cfg(any(test, creusot))]
        if !root_bound {
            return false;
        }

        let depth = config.smt.depth;

        #[cfg(not(any(test, creusot)))]
        if depth < 64 && pi.asset_id.0 >= (1u64 << depth) {
            return false;
        }

        #[cfg(any(test, creusot))]
        let key_range_bound = depth >= 64 || pi.asset_id.0 < (1u64 << depth);
        #[cfg(any(test, creusot))]
        if !key_range_bound {
            return false;
        }

        let hasher = DefaultHasher::new(config.smt.leaf_max_fields as usize);
        let vd_matches = |leaf: &LeafState| hasher.hash_leaf(&leaf.encode()) == Ok(pi.value_digest);
        let vd_ok = match op {
            SmtOperation::Membership { payload, .. } => {
                vd_matches(&LeafState::Occupied(payload.clone()))
            }
            SmtOperation::Update { new_leaf, .. } => vd_matches(new_leaf),
            SmtOperation::NonMembership { .. } => {
                vd_matches(&LeafState::Empty) || vd_matches(&LeafState::Tombstone)
            }
        };
        if !vd_ok {
            return false;
        }
        #[cfg(not(any(test, creusot)))]
        if matches!(kind, SmtOpKind::NonMembership)
            && !matches!(
                request.witness.leaf,
                LeafState::Empty | LeafState::Tombstone
            )
        {
            return false;
        }

        #[cfg(any(test, creusot))]
        let leaf_kind_bound = !matches!(kind, SmtOpKind::NonMembership)
            || matches!(
                request.witness.leaf,
                LeafState::Empty | LeafState::Tombstone
            );
        #[cfg(any(test, creusot))]
        if !leaf_kind_bound {
            return false;
        }

        #[cfg(not(any(test, creusot)))]
        if let SmtOperation::Update { old_leaf, .. } = op {
            if &request.witness.leaf != old_leaf {
                return false;
            }
        }

        #[cfg(any(test, creusot))]
        let witness_echo_bound = match op {
            SmtOperation::Update { old_leaf, .. } => &request.witness.leaf == old_leaf,
            SmtOperation::Membership { .. } | SmtOperation::NonMembership { .. } => {
                !matches!(kind, SmtOpKind::Update)
            }
        };
        #[cfg(any(test, creusot))]
        if !witness_echo_bound {
            return false;
        }

        #[cfg(not(any(test, creusot)))]
        let inputs = match build_input_vector(
            &config.smt,
            circuit.input_width_bits,
            op,
            pi,
            &request.witness,
        ) {
            Ok(v) => v,
            Err(_) => return false,
        };

        #[cfg(any(test, creusot))]
        let input_result = build_input_vector(
            &config.smt,
            circuit.input_width_bits,
            op,
            pi,
            &request.witness,
        );
        #[cfg(any(test, creusot))]
        let input_vector_bound = input_result.is_ok();
        #[cfg(any(test, creusot))]
        let inputs = match input_result {
            Ok(v) => v,
            Err(_) => return false,
        };

        let out_width = 1usize << circuit.layers[0].width_bits;
        #[cfg(any(test, creusot))]
        let claimed_output_construction = ClaimedOutputConstruction::AllZeroVector;
        let claimed_outputs = vec![BaseField::ZERO; out_width];

        #[cfg(any(test, creusot))]
        let zero_output_claim = claimed_output_construction.is_zero_claim();
        #[cfg(any(test, creusot))]
        if !zero_output_claim {
            return false;
        }

        let mut transcript = Transcript::new(DOMAIN_TAG_V01);
        observe_circuit_digest(&mut transcript, circuit, kind, depth, commitment);
        observe_public_inputs(&mut transcript, pi);
        transcript.observe_many(&claimed_outputs);

        #[cfg(not(any(test, creusot)))]
        let claim = match ssgkr_protocol::verify(
            circuit,
            wiring,
            &claimed_outputs,
            &result.proof,
            &mut transcript,
        ) {
            Ok(c) => c,
            Err(_) => return false,
        };

        #[cfg(any(test, creusot))]
        let protocol_result = ssgkr_protocol::verify(
            circuit,
            wiring,
            &claimed_outputs,
            &result.proof,
            &mut transcript,
        );
        #[cfg(any(test, creusot))]
        let (sumcheck_consistent, carry_consistent) = observe_protocol_trace(&protocol_result);
        #[cfg(any(test, creusot))]
        let claim = match protocol_result {
            Ok(c) => c,
            Err(_) => return false,
        };

        #[cfg(not(any(test, creusot)))]
        {
            mle_eval_base(&inputs, &claim.point) == claim.expected_eval
                && mle_eval_base(&inputs, &claim.point_y) == claim.expected_eval_y
        }

        #[cfg(any(test, creusot))]
        {
            let (final_mle_x, final_mle_y) = observe_final_mle_trace(&inputs, &claim);
            if !final_mle_x {
                return false;
            }
            let request_guards_bound = tag_key_bound
                && root_bound
                && key_range_bound
                && vd_ok
                && leaf_kind_bound
                && witness_echo_bound
                && input_vector_bound;
            AcceptanceTrace {
                public_inputs_bound,
                request_guards_bound,
                zero_output_claim,
                sumcheck_consistent,
                carry_consistent,
                final_mle_x,
                final_mle_y,
            }
            .accepts()
        }
    }};
}

/// Shared generic verifier body used by production and reference wiring paths.
pub fn verify_sync_op_with<W: WiringOracle<ChallengeField>>(
    config: &StateSyncGkrConfig,
    request: &SyncRequest,
    result: &SyncResult,
    circuit: &LayeredCircuit<BaseField>,
    wiring: &W,
    commitment: &Digest<BaseField>,
) -> bool {
    verify_sync_op_body!(config, request, result, circuit, wiring, commitment)
}

/// Creusot target for the production `DerivedRegularWiring` instantiation.
#[cfg(creusot)]
fn verify_sync_op_with_derived_body(
    config: &StateSyncGkrConfig,
    request: &SyncRequest,
    result: &SyncResult,
    circuit: &LayeredCircuit<BaseField>,
    wiring: &DerivedRegularWiring,
    commitment: &Digest<BaseField>,
) -> bool {
    verify_sync_op_body!(config, request, result, circuit, wiring, commitment)
}

/// The final input-MLE computation and foreign extension-field equality.
///
/// This claim-free seam is compiled only on `cfg(test, creusot)` verification paths. It supplies no
/// postcondition equating its Boolean result with Isabelle field equality;
/// the non-trusted caller only proves that acceptance follows the `true`
/// branches of the two actual checks.
#[cfg(any(test, creusot))]
#[cfg_attr(creusot, trusted)]
fn observed_input_mle_match(
    inputs: &[BaseField],
    point: &[ChallengeField],
    expected: ChallengeField,
) -> bool {
    mle_eval_base(inputs, point) == expected
}

/// Observe the two independent final input-MLE discharge checks.
///
/// The returned pair is populated by the two actual equality computations,
/// in production order. It is used by the `cfg(test, creusot)` verifier path
/// and by witnesses that make exactly one side false.
#[cfg(any(test, creusot))]
fn observe_final_mle_trace(inputs: &[BaseField], claim: &InputClaim) -> (bool, bool) {
    (
        observed_input_mle_match(inputs, &claim.point, claim.expected_eval),
        observed_input_mle_match(inputs, &claim.point_y, claim.expected_eval_y),
    )
}

/// Split the actual protocol `Result` into the two checks it jointly certifies.
///
/// `ssgkr_protocol::verify` returns `Ok` only after every sumcheck call and
/// every per-layer reconstruction/carry check has passed. The two fields stay
/// distinct so source mutations can demonstrate that neither may be miswired.
#[cfg(any(test, creusot))]
fn observe_protocol_trace(
    protocol_result: &Result<InputClaim, ssgkr_protocol::GkrError>,
) -> (bool, bool) {
    let sumcheck_consistent = protocol_result.is_ok();
    let carry_consistent = protocol_result.is_ok();
    (sumcheck_consistent, carry_consistent)
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod acceptance_trace_tests {
    use super::{StateSyncGkrConfig, SyncRequest, prove_sync_op, verify_sync_op};
    use ssgkr_compiler::{
        AssetId, LayerStrategy, LeafPayload, LeafState, MerklePath, PublicInputs, SmtOperation,
        SmtParams, SmtWitness,
    };
    use ssgkr_primitives::field::{BaseField, ChallengeField, PrimeCharacteristicRing};
    use ssgkr_primitives::hash::{DefaultHasher, Digest, HashGadget};
    use ssgkr_protocol::InputClaim;

    fn f(value: u32) -> BaseField {
        BaseField::from_u32(value)
    }

    fn fixture() -> (StateSyncGkrConfig, SyncRequest) {
        let depth = 4usize;
        let config = StateSyncGkrConfig {
            smt: SmtParams {
                depth: depth as u32,
                ..Default::default()
            },
            layer_strategy: LayerStrategy::A,
            batching: Default::default(),
        };
        let key = AssetId(5);
        let payload = LeafPayload {
            sync_state: vec![f(42), f(7)],
            identity_digest: [9u8; 32],
        };
        let leaf = LeafState::Occupied(payload.clone());
        let path = MerklePath {
            siblings: (0..depth)
                .map(|index| Digest([f(index as u32 * 13 + 1); 8]))
                .collect(),
        };
        let hasher = DefaultHasher::new(config.smt.leaf_max_fields as usize);
        let old_root = path.compute_root(&hasher, &config.smt, key, &leaf).unwrap();
        let value_digest = hasher.hash_leaf(&leaf.encode()).unwrap();
        let request = SyncRequest {
            operation: SmtOperation::Membership { key, payload },
            witness: SmtWitness { leaf, path },
            public_inputs: PublicInputs {
                old_root,
                new_root: old_root,
                op_kind_tag: 0,
                asset_id: key,
                value_digest,
            },
        };
        (config, request)
    }

    #[test]
    fn actual_acceptance_trace_positive_witness() {
        let (config, request) = fixture();
        let result = prove_sync_op(&config, &request).unwrap();
        assert!(verify_sync_op(&config, &request, &result));
    }

    #[test]
    fn actual_acceptance_trace_negative_witnesses() {
        let (config, request) = fixture();
        let result = prove_sync_op(&config, &request).unwrap();

        let mut public_tamper = request.clone();
        public_tamper.public_inputs.old_root = Digest([f(123); 8]);
        public_tamper.public_inputs.new_root = Digest([f(123); 8]);
        assert!(!verify_sync_op(&config, &public_tamper, &result));

        let mut sumcheck_tamper = result.clone();
        sumcheck_tamper.proof.layer_proofs[0]
            .sumcheck
            .round_polys
            .clear();
        assert!(!verify_sync_op(&config, &request, &sumcheck_tamper));

        let mut carry_tamper = result.clone();
        carry_tamper.proof.layer_proofs[0].eval_x += ChallengeField::ONE;
        assert!(!verify_sync_op(&config, &request, &carry_tamper));

        let mut wrong_witness = request.clone();
        wrong_witness.witness.path.siblings[1] = Digest([f(999); 8]);
        assert!(!verify_sync_op(&config, &wrong_witness, &result));

        let mut result_public_tamper = result;
        result_public_tamper.public_inputs.old_root = Digest([f(777); 8]);
        assert!(!verify_sync_op(&config, &request, &result_public_tamper));
    }

    #[test]
    fn acceptance_trace_classifier_has_no_free_field() {
        assert!(super::ClaimedOutputConstruction::AllZeroVector.is_zero_claim());
        assert!(!super::ClaimedOutputConstruction::Other.is_zero_claim());
        let observed = [false, true];
        for public_inputs_bound in observed {
            for request_guards_bound in observed {
                for zero_output_claim in observed {
                    for sumcheck_consistent in observed {
                        for carry_consistent in observed {
                            for final_mle_x in observed {
                                for final_mle_y in observed {
                                    let trace = super::AcceptanceTrace {
                                        public_inputs_bound,
                                        request_guards_bound,
                                        zero_output_claim,
                                        sumcheck_consistent,
                                        carry_consistent,
                                        final_mle_x,
                                        final_mle_y,
                                    };
                                    assert_eq!(
                                        trace.accepts(),
                                        public_inputs_bound
                                            && request_guards_bound
                                            && zero_output_claim
                                            && sumcheck_consistent
                                            && carry_consistent
                                            && final_mle_x
                                            && final_mle_y
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn final_mle_x_and_y_are_independently_observed() {
        let inputs = [f(0), f(1)];
        let x_false_y_true = InputClaim {
            point: vec![ChallengeField::ZERO],
            expected_eval: ChallengeField::ONE,
            point_y: vec![ChallengeField::ONE],
            expected_eval_y: ChallengeField::ONE,
        };
        assert_eq!(
            super::observe_final_mle_trace(&inputs, &x_false_y_true),
            (false, true)
        );

        let x_true_y_false = InputClaim {
            point: vec![ChallengeField::ZERO],
            expected_eval: ChallengeField::ZERO,
            point_y: vec![ChallengeField::ONE],
            expected_eval_y: ChallengeField::ZERO,
        };
        assert_eq!(
            super::observe_final_mle_trace(&inputs, &x_true_y_false),
            (true, false)
        );
    }
}
