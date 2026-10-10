//! SMT domain types and the NATIVE verification semantics.
//!
//! `smt_valid_native` below is the Rust transcription of the Isabelle
//! `smt_valid` in `formal/isabelle/SMT_Circuit_Compiler_Correctness/SMT_Semantics.thy`
//! and defines the meaning
//! standard Theorem A compares the compiled circuit against, and the test
//! oracle for compiler correctness tests. Keep it spec-literal and slow;
//! it is never on the proving hot path.

use ssgkr_primitives::field::BaseField;
use ssgkr_primitives::hash::{Digest, HashError, HashGadget, KeccakDigestBytes};

use crate::params::SmtParams;

// Named imports on purpose (the prelude glob would shadow the std derives
// and `vec!` - see the note in ssgkr-primitives::hash).
#[cfg(creusot)]
use creusot_std::prelude::{
    DeepModel, Int, Seq, ensures, invariant, logic, pearlite, snapshot, trusted, variant,
};
#[cfg(creusot)]
use ssgkr_primitives::hash::{h_leaf_enc, h_node};

/// Sequential AssetID key (monotone counter allocated by the RWA
/// Registry contract; uniqueness is enforced by the verified state
/// transition, not by this crate).
///
/// Under `--cfg creusot` the verifier's `PartialOrd`/`Ord` derives need a
/// `DeepModel` whose model type carries a logical order; the key models as
/// the mathematical integer of its `u64` (spelled out below - the derived
/// wrapper model would lack `OrdLogic`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AssetId(pub u64);

#[cfg(creusot)]
impl DeepModel for AssetId {
    type DeepModelTy = Int;

    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { self.0@ }
    }
}

/// Leaf payload: asset sync state plus the OFF-circuit keccak identity
/// digest (opaque here; in-circuit hashing is Poseidon2 only).
///
/// `Clone`/`PartialEq`/`Eq` are derived only outside Creusot builds: the
/// payload carries raw field elements, so it takes the same black-box
/// boundary treatment as `Digest` (identity deep model + trusted `eq` =
/// logical equality + trusted `clone` = identity; see
/// ssgkr-primitives::hash) - the derived versions carry no value contract
/// at the pinned rev.
#[derive(Debug)]
#[cfg_attr(not(creusot), derive(Clone, PartialEq, Eq))]
pub struct LeafPayload {
    /// Asset synchronization state, already encoded as field elements by
    /// the caller (encoding convention is part of the registry contract,
    /// not of this prover).
    pub sync_state: Vec<BaseField>,
    /// keccak256 identity digest, computed off-circuit (self-defense
    /// linkage to the registry identity; D-28).
    pub identity_digest: KeccakDigestBytes,
}

#[cfg(creusot)]
impl DeepModel for LeafPayload {
    type DeepModelTy = LeafPayload;

    #[logic(open, inline)]
    fn deep_model(self) -> Self {
        self
    }
}

#[cfg(creusot)]
impl PartialEq for LeafPayload {
    #[trusted]
    #[ensures(result == (self.deep_model() == other.deep_model()))]
    fn eq(&self, other: &Self) -> bool {
        self.sync_state == other.sync_state && self.identity_digest == other.identity_digest
    }
}

#[cfg(creusot)]
impl Eq for LeafPayload {}

#[cfg(creusot)]
impl Clone for LeafPayload {
    // `trusted`: cloning opaque field values is the same black-box claim
    // as their equality ("copy is identity"); the derived clone carries
    // no value contract at the pinned rev.
    #[trusted]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        LeafPayload {
            sync_state: self.sync_state.clone(),
            identity_digest: self.identity_digest,
        }
    }
}

/// Three-state leaf convention (D-28): `Tombstone` preserves
/// non-membership semantics after deletion.
///
/// Isabelle: `datatype 'v leaf_state = Empty | Occupied 'v | Tombstone`.
///
/// Under `--cfg creusot` the containers holding a leaf state need it to
/// carry a `DeepModel`; every field type has one (`LeafPayload` via its
/// black-box boundary impl), so it is simply derived. `PartialEq`/`Eq`
/// are derived only outside Creusot builds: the verifier's derived `eq`
/// carries NO contract at the pinned rev (its result is logically
/// opaque), so the Creusot build takes the derive-equivalent impl below,
/// whose "eq IS deep-model equality" contract is PROVEN (not trusted -
/// the body is pure structure over the spec-carrying `LeafPayload` eq).
#[derive(Clone, Debug, Default)]
#[cfg_attr(not(creusot), derive(PartialEq, Eq))]
#[cfg_attr(creusot, derive(DeepModel))]
pub enum LeafState {
    /// Never-occupied slot.
    #[default]
    Empty,
    /// Occupied slot with payload.
    Occupied(LeafPayload),
    /// Deleted slot (distinct from `Empty` for non-membership proofs).
    Tombstone,
}

#[cfg(creusot)]
impl PartialEq for LeafState {
    #[ensures(result == (self.deep_model() == other.deep_model()))]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (LeafState::Empty, LeafState::Empty) => true,
            (LeafState::Tombstone, LeafState::Tombstone) => true,
            (LeafState::Occupied(a), LeafState::Occupied(b)) => a == b,
            _ => false,
        }
    }
}

#[cfg(creusot)]
impl Eq for LeafState {}

/// Logic-level name for the leaf-state field encoding: the UNINTERPRETED
/// graph of [`LeafState::encode`].
///
/// Mirror status (decision-1 seam): the Isabelle `encode` is concrete in
/// its TAG STRUCTURE but abstract in the payload encoder (`encp` is a
/// model parameter - "the registry contract fixes the concrete
/// convention"). On the Rust side even the tag values sit behind the
/// opaque field constructors (`BaseField::{ZERO, ONE, TWO}` - plonky3
/// black box, design B.6), so the whole encoding is mirrored as one
/// uninterpreted symbol. NOTHING is claimed about the encoding values
/// (no tags, no lengths, no injectivity - mapping #2 stays open); the
/// symbol exists so that `h_leaf` below can be composed the way the
/// model composes `h_leaf` with a leaf state.
#[cfg(creusot)]
#[logic(opaque)]
#[allow(unused_variables)]
pub fn leaf_encoding(l: LeafState) -> Seq<BaseField> {
    dead
}

/// Logic mirror of the Isabelle abstract `h_leaf :: 'v leaf_state => 'd`
/// (`SMT_Semantics.thy` locale parameter): the composition of the
/// gadget's encoding-domain hash with the leaf encoding - exactly how
/// the executable path computes it (`hash_leaf(leaf.encode())`).
#[cfg(creusot)]
#[logic(open)]
pub fn h_leaf<H>(h: H, leaf: LeafState) -> Digest<BaseField> {
    pearlite! { h_leaf_enc(h, leaf_encoding(leaf)) }
}

/// Logic mirror of `SMT_Sem.path_root`, recursion spelled over an index
/// into the sibling sequence (Creusot's sequence library lacks the
/// `S[0..len] = S` extensionality a tail-list phrasing needs, so the
/// index-based spelling is the definitional form; structure per step is
/// the model's, literally: low key bit selects the compress order, the
/// key steps down one bit).
///
/// Notation gap (tool boundary, honest scope): the model steps with
/// `key mod 2` / `key div 2` over `nat`; this mirror steps with
/// `key & 1` / `key >> 1` over `u64`. At the pinned rev Creusot's
/// default integer prelude declares `bw_and`/`shr` WITHOUT any axioms
/// (they are uninterpreted, and the bitwise-mode alternative changes
/// the whole function's integer model), so the arithmetic identity
/// `x & 1 = x mod 2 /\ x >> 1 = x div 2` is not machine-available; the
/// program text uses exactly these bit operations, so the mirror is
/// syntactically faithful to the CODE and structurally faithful to the
/// MODEL, with the bit/arithmetic identification carried as a documented
/// tool boundary (rev-needed: axiomatized bit ops or a bridged prelude).
#[cfg(creusot)]
#[logic]
#[variant(sib.len() - i)]
pub fn path_root_from<H>(
    h: H,
    leaf: Digest<BaseField>,
    key: u64,
    sib: Seq<Digest<BaseField>>,
    i: Int,
) -> Digest<BaseField> {
    pearlite! {
        if i < 0 || i >= sib.len() { leaf }
        else {
            path_root_from(
                h,
                if key & 1u64 == 0u64 { h_node(h, leaf, sib[i]) } else { h_node(h, sib[i], leaf) },
                key >> 1u64,
                sib,
                i + 1,
            )
        }
    }
}

/// `SMT_Sem.path_root` proper (fold from the deepest sibling).
#[cfg(creusot)]
#[logic(open)]
pub fn path_root<H>(
    h: H,
    leaf: Digest<BaseField>,
    key: u64,
    sib: Seq<Digest<BaseField>>,
) -> Digest<BaseField> {
    pearlite! { path_root_from(h, leaf, key, sib, 0) }
}

/// Logic mirror of `SMT_Sem.path_ok`: the two guards plus the root
/// equation. The key-range guard is spelled in the machine form
/// (`depth < 64 ==> key < 1 << depth`); combined with the u64 key space
/// it implies the model's unconditional `key < 2 ^ depth` in every case
/// (for `depth >= 64`, `key < 2^64 <= 2^depth` holds by type).
#[cfg(creusot)]
#[logic(open)]
pub fn path_ok<H>(
    h: H,
    depth: u32,
    leaf: LeafState,
    key: u64,
    sib: Seq<Digest<BaseField>>,
    root: Digest<BaseField>,
) -> bool {
    pearlite! {
        sib.len() == depth@
            && (depth@ < 64 ==> key@ < (1u64 << depth)@)
            && path_root(h, h_leaf(h, leaf), key, sib) == root
    }
}

impl LeafState {
    /// Domain-separated field encoding fed to the leaf pre-hash.
    ///
    /// Encoding convention (frozen with S-4/S-6): a 1-element tag
    /// (0 = Empty, 1 = Occupied, 2 = Tombstone) followed by the payload
    /// encoding for `Occupied` (sync state words, then the keccak digest
    /// packed little-endian into 30-bit limbs - see `pack_keccak_digest`).
    /// Encodings longer than the instance bound `SmtParams::leaf_max_fields`
    /// are outside the leaf hash's domain (structural error at hash time,
    /// 2d ping-pong CR fix); the length-binding lives in the hash's
    /// `leaf_fold` pre-image, not here.
    ///
    /// Creusot boundary treatment (decision-1 seam, flagged for
    /// supervisor re-adjudication): `trusted` with the pure GRAPH
    /// contract `result@ == leaf_encoding(*self)` - the result is THE
    /// function of the leaf state named by the uninterpreted symbol.
    /// This claims determinism ONLY (true of this body: pure structure
    /// plus opaque field constructors) and no encoding semantics
    /// whatsoever; it is forced because binding a program value to any
    /// logic-level name crosses the opaque-constructor boundary
    /// (`ZERO`/`ONE`/`TWO`, `from_u32` - design B.6), which no
    /// non-trusted contract can do. Without it, `h_leaf` (and with it
    /// the path_ok equation clause of `smt_valid_native`/`compute_root`)
    /// is not expressible at all. The machine-expressible minimal clause
    /// `result@.len() >= 1` (~ `encode_nonempty`) cannot ride along as a
    /// PROOF under `trusted`; it stays open with mapping #2 (tag
    /// separation etc.), carried honestly.
    #[cfg_attr(creusot, trusted)]
    #[cfg_attr(creusot, ensures(result@ == leaf_encoding(*self)))]
    pub fn encode(&self) -> Vec<BaseField> {
        use ssgkr_primitives::field::PrimeCharacteristicRing;
        match self {
            LeafState::Empty => vec![BaseField::ZERO],
            LeafState::Occupied(p) => {
                let mut out = vec![BaseField::ONE];
                out.extend_from_slice(&p.sync_state);
                out.extend(pack_keccak_digest(&p.identity_digest));
                out
            }
            LeafState::Tombstone => vec![BaseField::TWO],
        }
    }
}

/// Pack a 32-byte keccak digest into base-field elements (S-6 packing
/// convention, finalized in 2a).
///
/// The 256-bit digest is read little-endian and emitted as base-`2^30`
/// limbs (9 limbs). 30 bits, not 31: a full 31-bit limb can reach `2^31-1`,
/// which exceeds the KoalaBear modulus `p = 2^31 - 2^24 + 1` and would alias
/// under canonical reduction, breaking injectivity - and injectivity is what
/// binds distinct off-circuit identities to distinct leaf hashes (N2). Every
/// 30-bit limb is `< 2^30 < p`, so this map is unconditionally injective.
fn pack_keccak_digest(digest: &KeccakDigestBytes) -> Vec<BaseField> {
    use ssgkr_primitives::field::PrimeCharacteristicRing;
    const LIMB_BITS: u32 = 30;
    const LIMB_MASK: u64 = (1u64 << LIMB_BITS) - 1;
    let mut limbs = Vec::with_capacity(9);
    let mut acc: u64 = 0;
    let mut bits: u32 = 0;
    for &byte in digest {
        acc |= u64::from(byte) << bits;
        bits += 8;
        while bits >= LIMB_BITS {
            limbs.push(BaseField::from_u32((acc & LIMB_MASK) as u32));
            acc >>= LIMB_BITS;
            bits -= LIMB_BITS;
        }
    }
    if bits > 0 {
        limbs.push(BaseField::from_u32(acc as u32));
    }
    limbs
}

/// Merkle authentication path: sibling digests from leaf level upward.
///
/// Under `--cfg creusot` the containers holding a path need it to carry a
/// `DeepModel`; the digests model themselves (black-box boundary impl in
/// ssgkr-primitives::hash), so it is simply derived.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(creusot, derive(DeepModel))]
pub struct MerklePath {
    /// Sibling digests, deepest (leaf-adjacent) first.
    pub siblings: Vec<Digest<BaseField>>,
}

impl MerklePath {
    /// Recompute the root from a leaf state, its key and this path.
    ///
    /// Isabelle: `path_root` / `path_ok` - spec-literal transcription
    /// (key low bit selects left/right at the deepest level).
    ///
    /// R1 refinement anchor (Creusot-checked): Ok-necessity of ALL THREE
    /// clauses of `path_ok` (`SMT_Semantics.thy`) - the two guards
    /// (`length siblings = depth params`, `key < 2 ^ depth params`,
    /// spelled via the same `1u64 << depth` the guard uses; for
    /// `depth >= 64` the u64 key space cannot overflow the tree) AND the
    /// root equation: the returned digest IS
    /// `path_root (h_leaf leaf) key siblings` over the decision-1
    /// uninterpreted hash symbols (see [`path_root`]/[`h_leaf`]). The
    /// `Err` channel is the refinement side condition (the model's total
    /// functions have no structural-failure channel; the extra Rust-only
    /// failure is `hash_leaf`'s encoding bound).
    #[cfg_attr(creusot, ensures(match result {
        Ok(r) => self.siblings@.len() == params.depth@
            && (params.depth@ < 64 ==> key.0@ < (1u64 << params.depth)@)
            && r == path_root(*hasher, h_leaf(*hasher, *leaf), key.0, self.siblings@),
        Err(_) => true,
    }))]
    pub fn compute_root<H: HashGadget>(
        &self,
        hasher: &H,
        params: &SmtParams,
        key: AssetId,
        leaf: &LeafState,
    ) -> Result<Digest<BaseField>, SmtError> {
        if self.siblings.len() != params.depth as usize {
            return Err(SmtError::PathLengthMismatch {
                expected: params.depth as usize,
                found: self.siblings.len(),
            });
        }
        if params.depth < 64 && key.0 >= (1u64 << params.depth) {
            return Err(SmtError::KeyOutOfRange {
                key,
                depth: params.depth,
            });
        }

        let mut acc = hasher.hash_leaf(&leaf.encode())?;
        let mut bits = key.0;
        #[cfg_attr(creusot, invariant(
            path_root_from(*hasher, h_leaf(*hasher, *leaf), key.0, self.siblings@, 0)
                == path_root_from(*hasher, acc, bits, self.siblings@, produced.len())
        ))]
        for sibling in &self.siblings {
            acc = if bits & 1 == 0 {
                hasher.compress(&acc, sibling)
            } else {
                hasher.compress(sibling, &acc)
            };
            bits >>= 1;
        }
        Ok(acc)
    }
}

/// SMT operations whose verification the circuit proves.
///
/// Isabelle: `datatype 'v smt_op` - same three constructors.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(creusot, derive(DeepModel))]
pub enum SmtOperation {
    /// Prove `key` maps to exactly this occupied payload under `root`.
    Membership {
        /// Asset key.
        key: AssetId,
        /// Expected payload.
        payload: LeafPayload,
    },
    /// Prove `key` is Empty or Tombstone under `root`.
    NonMembership {
        /// Asset key.
        key: AssetId,
    },
    /// Prove the single-leaf transition `old_leaf -> new_leaf` at `key`
    /// transforms `old_root` into `new_root` (same sibling chain).
    Update {
        /// Asset key.
        key: AssetId,
        /// Prior leaf state.
        old_leaf: LeafState,
        /// New leaf state.
        new_leaf: LeafState,
    },
}

/// Operation KIND (the circuit-shape selector: circuit structure depends
/// only on the kind + params, never on the concrete witness - the
/// batching premise).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(creusot, derive(DeepModel))]
pub enum SmtOpKind {
    /// Membership proof.
    Membership,
    /// Non-membership proof.
    NonMembership,
    /// Single-leaf update.
    Update,
}

/// Logic mirror of `Cmp_Model.kind_of` (`Compiler_Model.thy`): the
/// three defining equations, constructor for constructor.
#[cfg(creusot)]
#[logic(open)]
pub fn kind_of(op: SmtOperation) -> SmtOpKind {
    match op {
        SmtOperation::Membership { .. } => SmtOpKind::Membership,
        SmtOperation::NonMembership { .. } => SmtOpKind::NonMembership,
        SmtOperation::Update { .. } => SmtOpKind::Update,
    }
}

impl SmtOperation {
    /// The circuit-shape selector of this operation.
    ///
    /// R1 refinement anchor (Creusot-checked): `kind()` = `kind_of`
    /// (`Compiler_Model.thy`), the 3-constructor 1:1 selector map.
    #[cfg_attr(creusot, ensures(result == kind_of(*self)))]
    pub fn kind(&self) -> SmtOpKind {
        match self {
            SmtOperation::Membership { .. } => SmtOpKind::Membership,
            SmtOperation::NonMembership { .. } => SmtOpKind::NonMembership,
            SmtOperation::Update { .. } => SmtOpKind::Update,
        }
    }
}

/// Private witness data accompanying an operation.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(creusot, derive(DeepModel))]
pub struct SmtWitness {
    /// The leaf state being authenticated (for Update: the OLD leaf).
    pub leaf: LeafState,
    /// Sibling chain for the leaf's key.
    pub path: MerklePath,
}

/// SMT-level errors.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(creusot, derive(DeepModel))]
pub enum SmtError {
    /// Sibling count differs from tree depth.
    PathLengthMismatch {
        /// Expected (= depth).
        expected: usize,
        /// Found.
        found: usize,
    },
    /// Key does not fit in the tree's key space.
    KeyOutOfRange {
        /// Offending key.
        key: AssetId,
        /// Tree depth.
        depth: u32,
    },
    /// Leaf encoding violates the structural bound (`leaf_max_fields`) or is
    /// empty - outside the collision-resistant leaf hash's domain (2d
    /// ping-pong CR fix). Oversized encodings are a structural error, never
    /// hashed lossily.
    LeafEncoding(HashError),
}

impl From<HashError> for SmtError {
    fn from(e: HashError) -> Self {
        SmtError::LeafEncoding(e)
    }
}

/// NATIVE operation semantics: the meaning standard (test oracle).
///
/// Isabelle: `smt_valid` - keep the three clauses literally in sync.
/// Returns Ok(()) iff the operation holds between `old_root` and
/// `new_root` with the given witness.
///
/// R1 refinement anchor (Creusot-checked): on `Ok(b)`, `b` is EQUAL to
/// the `smt_valid` clause conjunction (`SMT_Semantics.thy`) - the full
/// three-clause iff, clause-for-clause, `path_ok` included (decision-1
/// uninterpreted hash symbols, see [`path_ok`]):
///   Membership k v   ~ `root' = root /\ leaf = Occupied v /\ path_ok leaf k sib root`
///   NonMembership k  ~ `root' = root /\ (leaf = Empty \/ Tombstone) /\ path_ok leaf k sib root`
///   Update k old new ~ `leaf = old /\ path_ok old k sib root /\ path_ok new k sib root'`
/// Digest equality IS logical equality here (identity deep model, see
/// ssgkr-primitives::hash). `Err` cases are the refinement side
/// condition (the model's total functions have no structural-failure
/// channel; the Rust-only failures are the path guards and the leaf
/// encoding bound, both surfaced as errors instead of `false`).
#[cfg_attr(creusot, ensures(match result {
    Ok(b) => b == match op {
        SmtOperation::Membership { key, payload } =>
            *new_root == *old_root
                && witness.leaf == LeafState::Occupied(*payload)
                && path_ok(*hasher, params.depth, witness.leaf, key.0,
                           witness.path.siblings@, *old_root),
        SmtOperation::NonMembership { key } =>
            *new_root == *old_root
                && (witness.leaf == LeafState::Empty
                    || witness.leaf == LeafState::Tombstone)
                && path_ok(*hasher, params.depth, witness.leaf, key.0,
                           witness.path.siblings@, *old_root),
        SmtOperation::Update { key, old_leaf, new_leaf } =>
            witness.leaf == *old_leaf
                && path_ok(*hasher, params.depth, *old_leaf, key.0,
                           witness.path.siblings@, *old_root)
                && path_ok(*hasher, params.depth, *new_leaf, key.0,
                           witness.path.siblings@, *new_root),
    },
    Err(_) => true,
}))]
pub fn smt_valid_native<H: HashGadget>(
    hasher: &H,
    params: &SmtParams,
    op: &SmtOperation,
    old_root: &Digest<BaseField>,
    new_root: &Digest<BaseField>,
    witness: &SmtWitness,
) -> Result<bool, SmtError> {
    match op {
        SmtOperation::Membership { key, payload } => {
            let leaf_ok = witness.leaf == LeafState::Occupied(payload.clone());
            let root = witness
                .path
                .compute_root(hasher, params, *key, &witness.leaf)?;
            Ok(new_root == old_root && leaf_ok && root == *old_root)
        }
        SmtOperation::NonMembership { key } => {
            let leaf_ok = matches!(witness.leaf, LeafState::Empty | LeafState::Tombstone);
            let root = witness
                .path
                .compute_root(hasher, params, *key, &witness.leaf)?;
            Ok(new_root == old_root && leaf_ok && root == *old_root)
        }
        SmtOperation::Update {
            key,
            old_leaf,
            new_leaf,
        } => {
            let leaf_ok = witness.leaf == *old_leaf;
            let root_old = witness.path.compute_root(hasher, params, *key, old_leaf)?;
            let root_new = witness.path.compute_root(hasher, params, *key, new_leaf)?;
            Ok(leaf_ok && root_old == *old_root && root_new == *new_root)
        }
    }
}
