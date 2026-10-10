//! Module 1 - SMT-GKR Circuit Compiler.
//!
//! Compiles sparse-Merkle-tree verification (membership / non-membership
//! / single-leaf update over the RWA-registry asset-state tree) into the
//! generic layered-circuit IR of `ssgkr-protocol`.
//!
//! Workload-SPECIFIC layer: this crate may know everything about the SMT
//! shape; the generic crates (`ssgkr-sumcheck`, `ssgkr-protocol`) must never
//! know about this one (dependency direction is a frozen boundary, S-1).
//!
//! # FV anchoring (Theorem A / refinement R1)
//!
//! - `smt::smt_valid_native` is the Rust transcription of the Isabelle
//!   `smt_valid` (the meaning standard). It is the TEST ORACLE: the
//!   compiled circuit accepts a witness iff this predicate holds.
//! - `compile` (structure) and `generate_witness` (assignment) split so
//!   that structure is cacheable across a batch.
//! - Correctness-ready design: the compiler is verified AGAINST the
//!   semantic spec, never against its own output.
//!
//! SEAL[S-4]: the pair (`smt_valid_native`, circuit acceptance
//! convention) is the Theorem A boundary, frozen at G1.

pub mod builder;
pub mod compile;
pub mod params;
pub mod smt;
pub mod witness;

pub use compile::{CompileError, InputLayout, compile, compile_with_hints, validate_unary_gates};
pub use params::{LayerStrategy, SmtParams};
pub use smt::{
    AssetId, LeafPayload, LeafState, MerklePath, SmtError, SmtOpKind, SmtOperation, SmtWitness,
    smt_valid_native,
};
pub use witness::{PublicInputs, build_input_vector, generate_witness};

/// Acceptance convention for compiled circuits (frozen with S-4):
/// a witness is ACCEPTING iff every wire of the OUTPUT layer equals zero
/// (constraint-difference encoding: each output wire is a constraint
/// residual).
///
/// FV-CONTRACT (Creusot, R2 #9 - design contract, NOT tool-checked):
///   #[ensures(result == Layered_Circuit.circuit_accept
///       (every output-layer wire is zero))]
/// TOOL WALL (R2 dev, honest carry-over - no machine clause): the
/// zero test dispatches through `F::is_zero`, a contract-free plonky3
/// trait method on a generic field (design B.6 black box), so there is
/// no logic-level "= 0" to state the iff against; and the iterator
/// `all` predicate closes over it. Held by the model
/// (`circuit_accept`, seal S-4) and the composition-equivalence /
/// circuit-level lattice batteries.
pub fn is_accepting<F: ssgkr_primitives::field::Field>(
    witness: &ssgkr_protocol::CircuitWitness<F>,
) -> bool {
    witness
        .layer_values
        .first()
        .is_some_and(|out| out.iter().all(|v| v.is_zero()))
}
