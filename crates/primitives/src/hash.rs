//! Hash gadget abstraction and the Poseidon2 default instance.
//!
//! The hash is a swappable unit behind [`HashGadget`]: replacing it means
//! swapping the circuit template plus re-instantiating the FV model's
//! abstract hash (no re-proof). The trait deliberately mirrors the two
//! abstract functions of the Isabelle spec (`formal/isabelle/`):
//!
//! - `hash_leaf`  ~ Isabelle `h_leaf` (mandatory leaf pre-hash),
//! - `compress`   ~ Isabelle `h_node` (2-to-1 node compression).
//!
//! # Concrete Poseidon2 instantiation (the pair the circuit mirrors)
//!
//! Both are the standard p3-merkle-tree construction over one width-16
//! permutation - not an invention:
//!
//! - `h_node(L, R)` = `TruncatedPermutation`: `perm([L || R])[0..8]`
//!   (one permutation, pure truncation, no feed-forward).
//! - `h_leaf(payload)` = `PaddingFreeSponge` (rate 8) run over the FIXED,
//!   LOSSLESS [`leaf_fold`] pre-image (see below): `ceil(width/8)` chained
//!   permutations in overwrite mode, output = final state`[0..8]`.
//!
//! # Leaf pre-image: bounded, length-bound, injective (the 2d-audit CR fix)
//!
//! The 2d-audit confirmed a CRITICAL soundness break: the previous fold
//! WRAPPED an arbitrary-length encoding onto 16 lanes (`s[1+(j%15)] += v`),
//! which is not injective - distinct valid leaves collided onto one
//! pre-image, so `h_leaf` collided without breaking Poseidon2 and a forged
//! Membership of a never-committed payload was accepted end-to-end
//! (`tests/audit_2d.rs`). The fix makes the pre-image LOSSLESS:
//!
//! - the maximum supported encoding length is the instance parameter
//!   `leaf_max_fields` (config; default [`DEFAULT_LEAF_MAX_FIELDS`]);
//!   encodings longer than the bound are a structural error, never hashed;
//! - the pre-image is FIXED-width ([`leaf_pre_width`], the bound + tag/len
//!   bookkeeping rounded up to a whole number of rate-8 blocks) and every
//!   lane is absorbed by the sponge - no lane is dropped or summed;
//! - layout: `pre[0] = tag` (R2-1 domain separation preserved: the
//!   circuit's `tag*(tag-2)` residual stays a genuine tag check),
//!   `pre[1] = encoding length`, `pre[2..2+len-1] =` the rest of the
//!   encoding VERBATIM, zero padding beyond.
//!
//! Why the explicit length lane: padding alone is NOT injective across
//! encodings of different lengths - `[t, a]` and `[t, a, 0]` pad to the same
//! vector, and the keccak identity limbs at the tail of an Occupied encoding
//! are attacker-chosen bytes, so "shift the limbs and zero the tail" forgeries
//! are constructible. Binding the length closes that class: encodings of
//! different lengths differ in `pre[1]`; encodings of equal length differ
//! somewhere in the verbatim region. Hence `leaf_fold` is injective on
//! encodings of length `1..=leaf_max_fields`, and `h_leaf` collisions now
//! require breaking Poseidon2 itself.
//!
//! Keccak note: the asset identity digest stored in a leaf payload is
//! computed OFF-circuit by the caller (RWA Registry side). It enters this
//! crate only as opaque bytes inside the payload; in-circuit hashing is
//! Poseidon2 exclusively.

use p3_field::PrimeCharacteristicRing;
use p3_koala_bear::{Poseidon2KoalaBear, default_koalabear_poseidon2_16};
use p3_symmetric::{
    CryptographicHasher, PaddingFreeSponge, PseudoCompressionFunction, TruncatedPermutation,
};

use crate::field::BaseField;

// Named imports on purpose: the creusot-std prelude glob would shadow the
// std `Clone`/`PartialEq` derives and the `vec!` macro with Creusot's
// spec-carrying versions and break the production derives in this module.
#[cfg(creusot)]
use creusot_std::prelude::{DeepModel, Int, Seq, ensures, logic, requires, trusted};

/// Creusot specifications absent from creusot-std at the pinned toolchain
/// rev:
/// - `usize::div_ceil`: the quotient/remainder unfolding of ceiling
///   division - the exact form the Isabelle mirror uses
///   (`formal/isabelle/SMT_Circuit_Compiler_Correctness/Leaf_Fold.thy`,
///   `leaf_pre_width_def`);
/// - `<[T]>::is_empty`: the plain std meaning (`len == 0`);
/// - `PrimeCharacteristicRing::from_u32`: NO clauses on purpose - field
///   constructors are behind the plonky3 black-box boundary (design B.6 /
///   R4), so the spec claims nothing and only makes the call admissible.
#[cfg(creusot)]
mod creusot_specs {
    use creusot_std::prelude::*;
    use p3_field::PrimeCharacteristicRing;

    use crate::field::BaseField;

    extern_spec! {
        impl usize {
            #[allow(dead_code)]
            #[requires(rhs@ > 0)]
            #[ensures(result@ == self@ / rhs@ + if self@ % rhs@ == 0 { 0 } else { 1 })]
            fn div_ceil(self, rhs: usize) -> usize;
        }

        impl<T> [T] {
            #[allow(dead_code)]
            #[ensures(result == (self@.len() == 0))]
            fn is_empty(&self) -> bool;
        }

        mod p3_field {
            trait PrimeCharacteristicRing {
                #[allow(dead_code)]
                fn from_u32(input: u32) -> Self;
            }
        }
    }
}

/// Digest width in base-field elements. 8 x ~31 bits ~ 248-bit digests
/// (~124-bit collision resistance), matching plonky3 Merkle conventions.
pub const DIGEST_WIDTH: usize = 8;

/// Sponge rate of the leaf hash (lanes absorbed per permutation).
pub const LEAF_SPONGE_RATE: usize = 8;

/// Default maximum leaf ENCODING length (in field elements, tag included)
/// the instance supports - the `SmtParams::leaf_max_fields` default.
///
/// 31 = 1 tag + up to 21 sync-state fields + 9 keccak limbs: at least twice
/// the plausible RWA asset-state schema envelope (degree metadata, regulatory
/// action/lock state, financial fields, maturity/rate, timestamps - spec
/// section 3.7), and `31 + 1` bookkeeping lanes round to EXACTLY four rate-8
/// sponge blocks. An instance with a bigger schema raises the config value
/// (a genesis parameter, like tree depth: re-instantiation, not redesign).
pub const DEFAULT_LEAF_MAX_FIELDS: usize = 31;

/// Width of the fixed leaf pre-image for a given encoding bound: tag lane +
/// length lane + `(leaf_max_fields - 1)` verbatim lanes, rounded up to whole
/// rate-8 sponge blocks (so the sponge absorbs EVERY lane in exact chunks).
///
/// R1 refinement anchor (Creusot-checked): the contract mirrors the Isabelle
/// side 1:1 (`formal/isabelle/SMT_Circuit_Compiler_Correctness/Leaf_Fold.thy`) - the
/// exact-value clause is `leaf_pre_width_def` (div_ceil in its
/// quotient/remainder form), the derived clauses are the lemmas
/// `leaf_pre_width_ge` and `leaf_pre_width_rate_blocks`. The `requires` is
/// the machine-width side condition only (the model is over unbounded `nat`).
#[cfg_attr(creusot, requires(leaf_max_fields@ + 8 <= usize::MAX@))]
#[cfg_attr(creusot, ensures(result@ == ((leaf_max_fields@ + 1) / 8 + if (leaf_max_fields@ + 1) % 8 == 0 { 0 } else { 1 }) * 8))]
#[cfg_attr(creusot, ensures(leaf_max_fields@ + 1 <= result@))]
#[cfg_attr(creusot, ensures(result@ % 8 == 0))]
pub fn leaf_pre_width(leaf_max_fields: usize) -> usize {
    (leaf_max_fields + 1).div_ceil(LEAF_SPONGE_RATE) * LEAF_SPONGE_RATE
}

/// Errors from leaf-payload hashing (the structural encoding bound).
///
/// Under `--cfg creusot` the verifier's `PartialEq` derive needs a
/// `DeepModel`; all fields are `usize`, so it is simply derived.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(creusot, derive(creusot_std::prelude::DeepModel))]
pub enum HashError {
    /// The leaf encoding exceeds the instance bound `leaf_max_fields`.
    /// Oversized encodings are OUTSIDE the supported domain and are never
    /// hashed (hashing a lossy reduction is what broke collision
    /// resistance; see the module docs).
    EncodingTooLong {
        /// Offending encoding length.
        len: usize,
        /// Instance bound (`leaf_max_fields`).
        max: usize,
    },
    /// The leaf encoding is empty (every `LeafState::encode` starts with a
    /// tag element, so this is a caller error).
    EmptyEncoding,
}

/// Fold a leaf ENCODING (length `1..=leaf_max_fields`) into the fixed,
/// LOSSLESS leaf pre-image of width [`leaf_pre_width`]`(leaf_max_fields)`.
///
/// Layout (injective by construction - see the module docs):
/// `pre[0] = encoding tag` (R2-1 domain separation: the circuit's
/// `tag*(tag-2)` residual reads this lane), `pre[1] = encoding length`,
/// `pre[2..2+len-1] = encoding[1..]` VERBATIM, zeros beyond. No wrapping,
/// no summing: distinct in-bound encodings yield distinct pre-images.
///
/// FV-CONTRACT (Creusot, R1 - designed, NOT yet tool-checked; see below):
///   #[requires(leaf_max_fields@ + 8 <= usize::MAX@)]      // machine width
///   #[requires(leaf_max_fields@ < 4294967296)]            // 2^32: the length
///       lane is `payload.len() as u32`, and `as` TRUNCATES silently - an
///       encoding longer than 2^32-1 would alias in the length lane and
///       break the injectivity the lane exists for. In-bound payloads
///       satisfy `len <= leaf_max_fields`, so bounding the config bound
///       suffices (2d-audit follow-up, partial-audit C finding).
///   #[ensures(match result {
///       Ok(v) => 1 <= payload@.len() && payload@.len() <= leaf_max_fields@
///           && v@.len() == leaf_pre_width          // ~ leaf_fold_length
///           && v@[0] == payload@[0]                // ~ tag lane (R2-1)
///           && forall<i> 1 <= i < payload@.len()
///                ==> v@[1 + i] == payload@[i],     // ~ verbatim region
///       Err(_) => !(1 <= payload@.len()
///           && payload@.len() <= leaf_max_fields@), // ~ domain premise
///   })]
///   #[ensures(injective over the in-bound encoding domain)]
///   (mirrors `Leaf_Fold.thy` `leaf_fold_def`/`leaf_fold_length`; the
///   injectivity clause is the model-side lemma `leaf_fold_inj` plus the
///   property test `leaf_fold_is_injective_on_in_bound_encodings`, not a
///   per-execution postcondition; length-lane VALUE and zero padding stay
///   behind the opaque field constructor = R4.)
///
/// Tool boundary (2026-07-11, Creusot 0.13.0-dev rev 7af97e00): attaching
/// ANY `ensures` also emits the RESULT TYPE INVARIANT obligation
/// `inv(Result<Vec<BaseField>, _>)`, and `inv(BaseField)` is an OPAQUE
/// predicate for the foreign field type - threading it through this body's
/// three mutations plus the window copy lands in one unsplittable VC that
/// no configured prover discharges (z3/cvc5/cvc4/alt-ergo, time 20s,
/// depth 12; every callee subgoal proves, `vc_leaf_fold` itself does not).
/// Carried as an R1 follow-up; the call-site specs it needs
/// (`is_empty`, `from_u32`) are already supplied in `creusot_specs`.
///
/// The two `requires` below ARE active (requires-only contracts impose
/// obligations on callers without claiming anything about the result,
/// so they sit outside the ensures/inv wall): the machine-width side
/// condition and the 2^32 cast-safety bound of the designed contract.
/// A side effect matters cross-crate: an un-contracted foreign function
/// carries an impossible precondition at call sites, so the requires-only
/// contract is also what makes `build_input_vector`'s calls admissible.
#[cfg_attr(creusot, requires(leaf_max_fields@ + 8 <= usize::MAX@))]
#[cfg_attr(creusot, requires(leaf_max_fields@ < 4294967296))]
pub fn leaf_fold(
    payload: &[BaseField],
    leaf_max_fields: usize,
) -> Result<Vec<BaseField>, HashError> {
    if payload.is_empty() {
        return Err(HashError::EmptyEncoding);
    }
    if payload.len() > leaf_max_fields {
        return Err(HashError::EncodingTooLong {
            len: payload.len(),
            max: leaf_max_fields,
        });
    }
    let mut pre = vec![BaseField::ZERO; leaf_pre_width(leaf_max_fields)];
    pre[0] = payload[0]; // tag lane (R2-1)
    pre[1] = BaseField::from_u32(payload.len() as u32); // length lane (injectivity)
    pre[2..2 + payload.len() - 1].copy_from_slice(&payload[1..]);
    Ok(pre)
}

/// A hash digest as base-field elements.
///
/// SEAL[S-6-adjacent]: digests cross the public-input boundary; their
/// width and field encoding are frozen together with `PublicInputs`.
///
/// `PartialEq`/`Eq` are derived only outside Creusot builds: under
/// `--cfg creusot` the verifier's `PartialEq` carries a spec that demands a
/// `DeepModel`, and the foreign field type cannot provide one (orphan
/// rule). The Creusot build instead takes the boundary impls below, which
/// restore digest equality WITH a logical meaning.
#[derive(Clone, Copy, Debug)]
#[cfg_attr(not(creusot), derive(PartialEq, Eq))]
pub struct Digest<F>(pub [F; DIGEST_WIDTH]);

/// Creusot boundary treatment for the black-box field type (design B.6):
/// field elements are opaque to the verifier, so a digest models itself
/// (identity deep model) and `eq` is trusted to BE logical equality of
/// those opaque values. This states the black-box claim "plonky3 field
/// equality is mathematical equality" exactly once; every later spec that
/// compares digests (`smt_valid_native`, `compute_root`, ...) reuses it.
#[cfg(creusot)]
impl DeepModel for Digest<BaseField> {
    type DeepModelTy = Digest<BaseField>;
    #[logic(open, inline)]
    fn deep_model(self) -> Self {
        self
    }
}

#[cfg(creusot)]
impl PartialEq for Digest<BaseField> {
    #[trusted]
    #[ensures(result == (self.deep_model() == other.deep_model()))]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

#[cfg(creusot)]
impl Eq for Digest<BaseField> {}

impl<F: PrimeCharacteristicRing + Copy> Digest<F> {
    /// The all-zero digest (empty-subtree convention at the leaf level).
    pub fn zero() -> Self {
        Digest([F::ZERO; DIGEST_WIDTH])
    }
}

/// Circuit-template handle for one hash invocation, consumed by the
/// circuit compiler (Module 1) when laying out per-level hash rounds.
///
/// v0.1 keeps this intentionally small: the compiler asks the gadget how
/// many GKR layers one 2-to-1 compression occupies under the chosen layer
/// strategy. Filled in by 2a together with `compile`.
#[derive(Clone, Debug)]
pub struct HashRoundTemplate {
    /// Number of Poseidon2 rounds (external + internal) in one permutation.
    pub rounds: usize,
    /// GKR layers contributed by one 2-to-1 node compression (a single
    /// Poseidon2 permutation) under the fused arithmetization: 1 initial
    /// linear layer + one layer per round. A leaf hash chains
    /// `leaf_pre_width / LEAF_SPONGE_RATE` permutations (the sponge), so it
    /// is that multiple of this. Advisory metadata; the compiler derives the
    /// real layout when it emits the gates.
    pub layers_per_compression: usize,
}

/// R4 logic-level hash seam (Creusot mirror of the Isabelle abstract
/// hash parameters, `SMT_Semantics.thy` locale `smt_semantics`):
/// UNINTERPRETED logic symbols, one per abstract function.
///
/// - `h_node` ~ Isabelle `h_node :: 'd => 'd => 'd`.
/// - `h_leaf_enc` is the encoding-domain factor of Isabelle
///   `h_leaf :: 'v leaf_state => 'd`: the model applies `h_leaf` to a
///   LEAF STATE, while the Rust trait method consumes the leaf's field
///   ENCODING, so the model's `h_leaf` is mirrored as the composition
///   `h_leaf_enc(gadget, encoding(leaf))` (spelled out as `h_leaf` in
///   `ssgkr-compiler::smt`, next to `LeafState::encode`).
///
/// The extra first argument threads the GADGET VALUE: the Isabelle
/// locale fixes one `(h_leaf, h_node)` pair per instance, and the Rust
/// counterpart of "this instance" is the gadget value (two gadgets with
/// different `leaf_max_fields` hash differently, so a global symbol
/// without it would be unsound).
///
/// The symbols are opaque on purpose: NOTHING is claimed about the hash
/// values (plonky3 black box, design B.6) - specs built on them state
/// interface conformance only ("the gadget computes SOME function of the
/// gadget value and its arguments, used the way the model uses h").
#[cfg(creusot)]
#[logic(opaque)]
#[allow(unused_variables)]
pub fn h_node<H>(h: H, left: Digest<BaseField>, right: Digest<BaseField>) -> Digest<BaseField> {
    dead
}

/// Encoding-domain factor of the model's `h_leaf` - see [`h_node`] docs.
#[cfg(creusot)]
#[logic(opaque)]
#[allow(unused_variables)]
pub fn h_leaf_enc<H>(h: H, enc: Seq<BaseField>) -> Digest<BaseField> {
    dead
}

/// Swappable in-circuit hash interface (Rust side of the abstract hash
/// pair (`h_leaf`, `h_node`) fixed in the Isabelle sketch).
///
/// R4 refinement anchor (Creusot-checked, interface conformance only):
/// the method contracts below bind each method's result to the
/// corresponding UNINTERPRETED hash symbol ([`h_node`]/[`h_leaf_enc`])
/// applied to the gadget value and the arguments. That states exactly
/// (a) arity/usage conformance with the Isabelle locale parameters and
/// (b) determinism per gadget instance - and NOTHING about the hash
/// values themselves (plonky3 black box, design B.6).
/// `hash_leaf` is PARTIAL: defined exactly on encodings of length
/// `1..=leaf_max_fields` (the Isabelle model restricts `h_leaf`'s domain
/// the same way); the `Err` channel carries no claim (refinement side
/// condition, as in `compute_root`).
pub trait HashGadget: Clone {
    /// 2-to-1 node compression (`h_node`).
    #[cfg_attr(creusot, ensures(result == h_node(*self, *left, *right)))]
    fn compress(&self, left: &Digest<BaseField>, right: &Digest<BaseField>) -> Digest<BaseField>;

    /// Leaf payload digesting (`h_leaf`). Mandatory pre-hash: raw payloads
    /// never enter `compress` directly. Errs on encodings outside the
    /// instance bound (structural limit; oversized data is never hashed).
    #[cfg_attr(creusot, ensures(match result {
        Ok(d) => d == h_leaf_enc(*self, payload@),
        Err(_) => true,
    }))]
    fn hash_leaf(&self, payload: &[BaseField]) -> Result<Digest<BaseField>, HashError>;

    /// Circuit template metadata for the compiler (Module 1).
    fn round_template(&self) -> HashRoundTemplate;
}

/// Default instance: Poseidon2 over KoalaBear, width 16 (rate 8).
#[derive(Clone)]
pub struct Poseidon2Gadget {
    sponge: PaddingFreeSponge<Poseidon2KoalaBear<16>, 16, LEAF_SPONGE_RATE, DIGEST_WIDTH>,
    compressor: TruncatedPermutation<Poseidon2KoalaBear<16>, 2, DIGEST_WIDTH, 16>,
    leaf_max_fields: usize,
}

impl Poseidon2Gadget {
    /// Construct with the plonky3 default KoalaBear round constants and the
    /// given leaf-encoding bound (`SmtParams::leaf_max_fields`).
    pub fn new(leaf_max_fields: usize) -> Self {
        let perm = default_koalabear_poseidon2_16();
        Self {
            sponge: PaddingFreeSponge::new(perm.clone()),
            compressor: TruncatedPermutation::new(perm),
            leaf_max_fields,
        }
    }

    /// The instance's leaf-encoding bound.
    pub fn leaf_max_fields(&self) -> usize {
        self.leaf_max_fields
    }

    /// The underlying width-16 permutation (for the transcript duplex).
    pub fn permutation() -> Poseidon2KoalaBear<16> {
        default_koalabear_poseidon2_16()
    }

    /// Leaf hash of an already-folded pre-image: the rate-8 sponge over the
    /// fixed [`leaf_pre_width`]-wide pre-image (`width / 8` permutations,
    /// overwrite mode, every lane absorbed). This is the exact function the
    /// compiled circuit's leaf gadget mirrors; [`HashGadget::hash_leaf`] is
    /// `hash_leaf_pre(leaf_fold(payload)?)`.
    pub fn hash_leaf_pre(&self, pre: &[BaseField]) -> Digest<BaseField> {
        debug_assert_eq!(pre.len(), leaf_pre_width(self.leaf_max_fields));
        debug_assert_eq!(pre.len() % LEAF_SPONGE_RATE, 0);
        Digest(self.sponge.hash_iter(pre.iter().copied()))
    }
}

impl Default for Poseidon2Gadget {
    fn default() -> Self {
        Self::new(DEFAULT_LEAF_MAX_FIELDS)
    }
}

impl HashGadget for Poseidon2Gadget {
    // Both methods are `trusted` under Creusot with the trait's interface
    // contracts restated: the bodies are plonky3 black-box computations
    // (design B.6), and the contracts claim only "the result is THE
    // function of (gadget value, arguments) named by the uninterpreted
    // symbol" - true of these bodies (pure, no interior mutability, no
    // ambient state), with zero claims about the digest values.
    #[cfg_attr(creusot, trusted)]
    #[cfg_attr(creusot, ensures(result == h_node(*self, *left, *right)))]
    fn compress(&self, left: &Digest<BaseField>, right: &Digest<BaseField>) -> Digest<BaseField> {
        Digest(self.compressor.compress([left.0, right.0]))
    }

    #[cfg_attr(creusot, trusted)]
    #[cfg_attr(creusot, ensures(match result {
        Ok(d) => d == h_leaf_enc(*self, payload@),
        Err(_) => true,
    }))]
    fn hash_leaf(&self, payload: &[BaseField]) -> Result<Digest<BaseField>, HashError> {
        // Sponge over the FIXED-width, LOSSLESS, length-bound fold: fixed
        // circuit shape (batching premise) + R2-1 tag lane + genuine
        // collision resistance (injective pre-image; module docs).
        Ok(self.hash_leaf_pre(&leaf_fold(payload, self.leaf_max_fields)?))
    }

    fn round_template(&self) -> HashRoundTemplate {
        // Poseidon2 width-16 KoalaBear: 8 external + 20 internal = 28 rounds.
        // Fused arithmetization: one permutation (a node compression) becomes
        // 1 initial linear layer + 28 round layers = 29 GKR layers; a leaf
        // hash chains `leaf_pre_width / 8` permutations. Advisory only -
        // `compile` derives the real layout when it emits the gates.
        HashRoundTemplate {
            rounds: 28,
            layers_per_compression: 29,
        }
    }
}

/// Convenience alias used across module boundaries.
pub type DefaultHasher = Poseidon2Gadget;

/// Off-circuit keccak identity digest, carried opaquely inside leaf
/// payloads. Produced by the caller (registry side), never recomputed
/// in-circuit.
pub type KeccakDigestBytes = [u8; 32];

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;

    fn f(x: u32) -> BaseField {
        BaseField::from_u32(x)
    }

    /// Tiny deterministic PRNG (no external rand crate).
    struct Lcg(u64);
    impl Lcg {
        fn new(seed: u64) -> Self {
            Lcg(seed ^ 0x9E37_79B9_7F4A_7C15)
        }
        fn next_u32(&mut self) -> u32 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (self.0 >> 32) as u32
        }
        fn below(&mut self, n: u32) -> u32 {
            self.next_u32() % n
        }
    }

    #[test]
    fn leaf_pre_width_rounds_to_rate_blocks() {
        assert_eq!(leaf_pre_width(DEFAULT_LEAF_MAX_FIELDS), 32); // 4 blocks
        assert_eq!(leaf_pre_width(7), 8);
        assert_eq!(leaf_pre_width(15), 16);
        assert_eq!(leaf_pre_width(23), 24);
    }

    #[test]
    fn leaf_fold_layout_tag_len_verbatim() {
        let enc = [f(1), f(10), f(20), f(30)];
        let pre = leaf_fold(&enc, DEFAULT_LEAF_MAX_FIELDS).unwrap();
        assert_eq!(pre.len(), 32);
        assert_eq!(pre[0], f(1), "slot 0 = tag (R2-1)");
        assert_eq!(pre[1], f(4), "slot 1 = encoding length");
        assert_eq!(&pre[2..5], &[f(10), f(20), f(30)], "verbatim rest");
        assert!(pre[5..].iter().all(|v| *v == BaseField::ZERO), "zero pad");
    }

    #[test]
    fn leaf_fold_enforces_the_structural_bound() {
        let long: Vec<BaseField> = (0..DEFAULT_LEAF_MAX_FIELDS as u32 + 1).map(f).collect();
        assert_eq!(
            leaf_fold(&long, DEFAULT_LEAF_MAX_FIELDS),
            Err(HashError::EncodingTooLong {
                len: DEFAULT_LEAF_MAX_FIELDS + 1,
                max: DEFAULT_LEAF_MAX_FIELDS
            })
        );
        assert_eq!(
            leaf_fold(&[], DEFAULT_LEAF_MAX_FIELDS),
            Err(HashError::EmptyEncoding)
        );
        // The bound itself is in-domain.
        let exact: Vec<BaseField> = (0..DEFAULT_LEAF_MAX_FIELDS as u32).map(f).collect();
        assert!(leaf_fold(&exact, DEFAULT_LEAF_MAX_FIELDS).is_ok());
    }

    /// Injectivity property: distinct in-bound encodings NEVER share a
    /// pre-image. Covers (a) the 2d-audit wrap-collision class, (b) the
    /// trailing-zero / length-shift class the length lane exists for, and
    /// (c) seeded random pairs across all length combinations.
    #[test]
    fn leaf_fold_is_injective_on_in_bound_encodings() {
        let max = DEFAULT_LEAF_MAX_FIELDS;

        // (a) The exact 2d-audit collision shape: same slot-sum, different
        // elements at former wrap partners (old fold: rest 0 and 15 -> slot 1).
        let mk = |s0: u32, s15: u32| {
            let mut e = vec![f(1)];
            let mut ss = vec![f(0); 16];
            ss[0] = f(s0);
            ss[15] = f(s15);
            e.extend(ss);
            e.extend((0..9).map(|i| f(i + 100))); // fixed limbs
            e
        };
        let a = mk(5, 0);
        let b = mk(3, 2);
        assert_ne!(a, b);
        assert_ne!(
            leaf_fold(&a, max).unwrap(),
            leaf_fold(&b, max).unwrap(),
            "former wrap-collision pair must fold apart"
        );

        // (b) Length-shift / trailing-zero class: e2 = e1 ++ zeros.
        let e1 = vec![f(1), f(7), f(9)];
        let mut e2 = e1.clone();
        e2.push(f(0));
        assert_ne!(
            leaf_fold(&e1, max).unwrap(),
            leaf_fold(&e2, max).unwrap(),
            "length lane must separate zero-extended encodings"
        );

        // (c) Seeded random pairs over all length combinations.
        let mut rng = Lcg::new(0x1EAF_C0DE);
        for len1 in 1..=max {
            for len2 in 1..=max {
                let e1: Vec<BaseField> = (0..len1).map(|_| f(rng.below(2_000_000_000))).collect();
                let mut e2: Vec<BaseField> =
                    (0..len2).map(|_| f(rng.below(2_000_000_000))).collect();
                if e1 == e2 {
                    e2[0] += f(1); // force distinct
                }
                assert_ne!(
                    leaf_fold(&e1, max).unwrap(),
                    leaf_fold(&e2, max).unwrap(),
                    "distinct encodings (len {len1} vs {len2}) must fold apart"
                );
            }
        }
    }

    #[test]
    fn hash_leaf_is_deterministic_and_separates_states() {
        let h = Poseidon2Gadget::default();
        let a = h.hash_leaf(&[f(0)]).unwrap(); // Empty
        let t = h.hash_leaf(&[f(2)]).unwrap(); // Tombstone
        let o = h.hash_leaf(&[f(1), f(42)]).unwrap(); // Occupied-ish
        assert_eq!(h.hash_leaf(&[f(0)]).unwrap(), a);
        assert_ne!(a, t);
        assert_ne!(a, o);
        assert_ne!(t, o);
    }
}
