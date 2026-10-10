//! Module 4 - the EXTERNAL PROOF BOUNDARY: canonical inner-proof
//! encoding, full circuit commitment, wrap statement, and the outer-SNARK
//! wrap adapter.
//!
//! GKR proofs are (a) not zero-knowledge and (b) larger than SNARK
//! proofs, so external exposure wraps them into a succinct SNARK over
//! BN254. Internally, GKR alone carries first-stage finality; the wrap
//! adds external compatibility + zk.
//!
//! v0.3 boundary freeze (PG-3): everything an external party consumes
//! is defined in this crate and nowhere else -
//!
//! - [`encoding`]: inner-proof-v1 canonical bytes (envelope, statement,
//!   proof payload; fail-closed decoder + frozen error taxonomy).
//! - [`commitment`]: the full circuit commitment (gate-level circuit
//!   identity; absorbed into the S-5 transcript by the facade and
//!   carried in the envelope).
//! - [`statement`]: wrap-statement-v1 (the outer proof's BN254 public
//!   inputs) + the KoalaBear -> BN254 field bridge (design B.6's
//!   separate verification item).
//!
//! Responsibility split at the boundary (frozen with PG-3): the DECODER
//! checks byte shape, versions and canonicality; the VERIFYING SIDE
//! (facade) checks the identity against its own config and recomputes
//! the circuit commitment (never trusting the wire); the INNER VERIFIER
//! checks the cryptography; the WRAP BACKEND proves exactly the inner
//! verifier's acceptance for the statement - it may reject, but it may
//! never widen what the inner verifier accepts.
//!
//! OPEN SEAM (never frozen - integration-seam rule): the concrete
//! backend is swappable by design behind [`WrapBackend`]; the D-27
//! candidate set is confirmed against the current external verifier
//! support matrix. What IS frozen is the boundary above (encoding,
//! commitment, statement), which every backend consumes unchanged.

pub use ssgkr_commitment as commitment;
pub mod encoding;
pub mod prepared;
#[cfg(feature = "host")]
pub mod risc0_destination_policy;
#[cfg(feature = "host")]
pub mod risc0_route_b_manifest;
#[cfg(feature = "host")]
pub mod settlement;
pub mod statement;

use ssgkr_compiler::{SmtOperation, SmtWitness};

use crate::statement::{WrapStatementV1, wrap_statement_v1};

/// Everything a backend needs to produce one outer proof: the CANONICAL
/// inner-proof bytes (the frozen boundary - backends never consume raw
/// in-memory proof structs) plus the operation and private witness the
/// internal verifier requires (seal S-4 witness-access model). The
/// witness stays private input on the backend side; only the wrap
/// statement becomes public.
#[derive(Clone, Copy, Debug)]
pub struct WrapInput<'a> {
    /// inner-proof-v1 canonical bytes ([`crate::encoding`]).
    pub encoded_inner: &'a [u8],
    /// The SMT operation being attested.
    pub operation: &'a SmtOperation,
    /// The private witness (leaf + path).
    pub witness: &'a SmtWitness,
}

/// One wrapped (outer) proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WrappedProof {
    /// Backend identifier tag (for routing/diagnostics, not consensus).
    pub backend: &'static str,
    /// The wrap statement the proof attests (the outer proof system's
    /// public inputs). The facade cross-checks this echo against its own
    /// computation before accepting the wrap.
    pub statement: WrapStatementV1,
    /// Backend-defined proof bytes (e.g. a Groth16 proof serialization
    /// for the external verifier's submission format).
    pub bytes: Vec<u8>,
}

/// Errors from wrapping.
#[derive(Clone, Debug)]
pub enum WrapError {
    /// Backend is not available in this build (real backends are
    /// feature/infrastructure-gated).
    BackendUnavailable {
        /// Which backend was requested.
        backend: &'static str,
    },
    /// Backend rejected the input.
    Rejected {
        /// Human-readable reason.
        reason: String,
    },
}

/// Swappable wrap backend: a PROVER of the wrap relation (the facade's
/// `wrap_relation` - decode + identity + internal-verifier acceptance),
/// nothing wider. A backend may reject inputs it cannot prove; it must
/// never accept an input the relation rejects.
///
/// Field-transport note: the 31-bit base field is re-encoded for the
/// BN254 scalar field by the frozen 31-bit-stride packing
/// ([`crate::statement`]); a backend circuit binding inner digests must
/// enforce that packing in-circuit - a SEPARATE verification obligation
/// (Refinement Scope Statement, design B.6), deliberately outside the
/// v0.1 core.
pub trait WrapBackend {
    /// Produce the outer proof for one wrap input.
    fn wrap(&self, input: &WrapInput<'_>) -> Result<WrappedProof, WrapError>;

    /// Backend tag (diagnostics).
    fn name(&self) -> &'static str;
}

/// Mock backend: decodes the envelope and echoes the correct statement
/// WITHOUT cryptographic content (bytes carry a fixed tag only). Exists
/// so the pipeline stays drivable end-to-end wherever the real backend's
/// infrastructure (prover toolchain, proving hardware) is absent; any
/// consumer treating its output as a proof is a configuration error,
/// which the loud tag makes greppable.
#[derive(Clone, Copy, Debug, Default)]
pub struct MockWrapBackend;

impl WrapBackend for MockWrapBackend {
    fn wrap(&self, input: &WrapInput<'_>) -> Result<WrappedProof, WrapError> {
        let env =
            encoding::decode_inner_proof(input.encoded_inner).map_err(|e| WrapError::Rejected {
                reason: format!("mock backend: undecodable inner proof: {e:?}"),
            })?;
        Ok(WrappedProof {
            backend: self.name(),
            statement: wrap_statement_v1(&env.identity, &env.public_inputs),
            bytes: b"MOCK-WRAP-NOT-A-PROOF".to_vec(),
        })
    }

    fn name(&self) -> &'static str {
        "mock"
    }
}
