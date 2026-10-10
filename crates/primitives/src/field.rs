//! Field selection and re-exported field traits.
//!
//! All generic code in this workspace bounds on the re-exported traits
//! below (never on `p3_field::...` paths directly), keeping the plonky3
//! surface swappable behind this adapter.

// Re-exported trait surface. This list is the complete field-trait
// vocabulary the rest of the workspace is allowed to use.
pub use p3_field::{
    ExtensionField, Field, PrimeCharacteristicRing, PrimeField32, PrimeField64,
    extension::BinomialExtensionField,
};

/// Base field: KoalaBear, p = 2^31 - 2^24 + 1.
///
/// Chosen for the Poseidon2 x^3 S-box (halves in-circuit/native hash cost
/// vs BabyBear's x^7) and the proven KoalaBear -> BN254 wrapping path.
/// Code and FV stay generic over `Field`; this alias is the default
/// instance, and swapping it is a re-instantiation, not a redesign.
pub type BaseField = p3_koala_bear::KoalaBear;

/// Degree of the binomial extension used for verifier challenges.
///
/// Degree 4 gives |EF| ~ 2^124 (soundness error budget denominator).
/// Raising the degree is a parameter change here, nowhere else.
pub const CHALLENGE_EXT_DEGREE: usize = 4;

/// Challenge field: verifier randomness is sampled from this extension
/// so that per-round soundness error (deg / |EF|) stays negligible.
pub type ChallengeField = BinomialExtensionField<BaseField, CHALLENGE_EXT_DEGREE>;
