//! Thin adapter over plonky3 `=0.4.3`.
//!
//! Every plonky3 surface used by this workspace is re-exported or wrapped
//! HERE and only here, so that a future upstream rebase or pin move is
//! localized to this single crate. No other workspace crate may name a
//! `p3_*` path directly.
//!
//! Design anchors (see `ARCHITECTURE.md`):
//! - Base field: KoalaBear (2^31 - 2^24 + 1); code stays generic over
//!   `Field`, KoalaBear is the default instance.
//! - Challenges: degree-4 binomial extension (~124-bit soundness budget);
//!   degree can be raised without structural change.
//! - In-circuit hash: Poseidon2 only. Leaf payloads are ALWAYS pre-hashed
//!   (a bare 2-to-1 compression function is not collision resistant).

pub mod field;
pub mod hash;
pub mod poseidon2_arith;
pub mod transcript;

pub use field::{BaseField, CHALLENGE_EXT_DEGREE, ChallengeField};
pub use hash::{
    DEFAULT_LEAF_MAX_FIELDS, DIGEST_WIDTH, DefaultHasher, Digest, HashError, HashGadget,
    LEAF_SPONGE_RATE, Poseidon2Gadget, leaf_fold, leaf_pre_width,
};
pub use transcript::Transcript;
