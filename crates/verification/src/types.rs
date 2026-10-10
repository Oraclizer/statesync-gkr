//! Host-facing request and result value types owned by the normative R3
//! verification layer and re-exported by the root facade.

use ssgkr_compiler::{PublicInputs, SmtOperation, SmtWitness};

/// One state-sync proving request handed to the prover stack.
#[derive(Clone, Debug)]
pub struct SyncRequest {
    /// The SMT operation to prove.
    pub operation: SmtOperation,
    /// Private witness (leaf + path) as known by the host state store.
    pub witness: SmtWitness,
    /// Public inputs asserted by the host.
    pub public_inputs: PublicInputs,
}

/// Result returned to the host after proving.
#[derive(Clone, Debug)]
pub struct SyncResult {
    /// The proved public inputs (echoed for binding).
    pub public_inputs: PublicInputs,
    /// The inner GKR proof.
    pub proof: ssgkr_protocol::GkrProof,
}
