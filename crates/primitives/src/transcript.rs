//! Fiat-Shamir transcript over a Poseidon2 duplex sponge.
//!
//! SEAL[S-5]: the observation ORDER is a frozen soundness-critical
//! convention. For one proof, the transcript observes exactly:
//!
//!   1. domain separation tag,
//!   2. circuit digest (structure commitment),
//!   3. public inputs (in `PublicInputs` field order),
//!   4. per-layer, in output-to-input order: the layer claim, then each
//!      sumcheck round polynomial in round order.
//!
//! Challenges are sampled from the degree-4 extension field. Any change
//! to this ordering is a G1-level design change, never an inline edit.

use p3_challenger::{CanObserve, CanSample, DuplexChallenger};
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
use p3_koala_bear::{KoalaBear, Poseidon2KoalaBear};

use crate::field::{BaseField, ChallengeField};
use crate::hash::{Digest, Poseidon2Gadget};

#[cfg(creusot)]
use creusot_std::prelude::trusted;

type Inner = DuplexChallenger<KoalaBear, Poseidon2KoalaBear<16>, 16, 8>;

/// Deterministic Fiat-Shamir transcript (prover and verifier run the
/// identical observation sequence; divergence = rejected proof).
///
/// FV-CONTRACT (Creusot, R2/R3):
///   #[ensures(prover and verifier transcripts fed identical observations
///             yield identical challenge sequences)]
///   Modeled abstractly in Isabelle as `transcript_sound` (random-oracle
///   style assumption on p3-challenger; plonky3 black-box boundary).
pub struct Transcript {
    inner: Inner,
}

// R2 note: every method below is `#[trusted]` under Creusot with ZERO
// claims (no requires/ensures). The whole transcript surface is the
// Fiat-Shamir black-box boundary (design B.3, `transcript_sound`
// assumption; the Isabelle model draws verifier randomness from
// `pmf_of_set` and never models the transcript). The trusted marker
// only grants callability to callers (the R1 claim-free spec class);
// determinism/soundness claims stay on the assumption side.
impl Transcript {
    /// Create a transcript seeded with a domain separation tag.
    #[cfg_attr(creusot, trusted)]
    pub fn new(domain_tag: &[u8]) -> Self {
        let mut inner = Inner::new(Poseidon2Gadget::permutation());
        // Absorb the tag as field elements (byte-wise embedding; cheap and
        // unambiguous for ASCII tags).
        for &b in domain_tag {
            inner.observe(BaseField::from_u8(b));
        }
        Self { inner }
    }

    /// Observe a single base-field element.
    #[cfg_attr(creusot, trusted)]
    pub fn observe_base(&mut self, x: BaseField) {
        self.inner.observe(x);
    }

    /// Observe a digest (e.g. roots, circuit digest).
    #[cfg_attr(creusot, trusted)]
    pub fn observe_digest(&mut self, d: &Digest<BaseField>) {
        for x in d.0 {
            self.inner.observe(x);
        }
    }

    /// Observe a slice of base-field elements (e.g. a round polynomial's
    /// coefficients, in coefficient order).
    #[cfg_attr(creusot, trusted)]
    pub fn observe_many(&mut self, xs: &[BaseField]) {
        for &x in xs {
            self.inner.observe(x);
        }
    }

    /// Observe an extension-field element by absorbing its base-field
    /// basis coefficients in order (unambiguous fixed-width encoding).
    #[cfg_attr(creusot, trusted)]
    pub fn observe_ext(&mut self, x: ChallengeField) {
        let coeffs =
            <ChallengeField as BasedVectorSpace<BaseField>>::as_basis_coefficients_slice(&x);
        for &c in coeffs {
            self.inner.observe(c);
        }
    }

    /// Sample one verifier challenge from the extension field.
    #[cfg_attr(creusot, trusted)]
    pub fn sample_challenge(&mut self) -> ChallengeField {
        self.inner.sample()
    }
}
