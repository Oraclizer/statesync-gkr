//! GKR protocol assembly over the sumcheck crate.
//!
//! GENERIC layer: no SMT/workload assumptions (modularity gate - this
//! crate must stay extractable together with `ssgkr-sumcheck`).
//!
//! # Protocol shape (Theorem B target)
//!
//! Starting from a claim about the OUTPUT layer's multilinear extension
//! at a random point, one sumcheck per layer (over the wiring identity in
//! `wiring.rs`) reduces it to a claim about the layer below, until the
//! INPUT layer, where the verifier (or the caller) evaluates the input
//! MLE directly. The final-claim handoff between layers uses the
//! [`ssgkr_sumcheck::Subclaim`] interface (seal S-2).
//!
//! Proof-object layout and transcript order are frozen by S-5; the layer
//! reduction algebra is 2a work, the shapes are fixed here.

pub mod circuit;
pub mod mle;
pub mod reduce;
pub mod wiring;

pub use circuit::{
    CircuitError, CircuitWitness, Gate, GateKind, Layer, LayeredCircuit, evaluate_circuit,
    gate_semantics,
};
pub use wiring::{
    DerivedRegularWiring, DerivedStats, FamilyTag, LayerHints, RegularWiring, WiringHints,
    WiringOracle,
};

use ssgkr_primitives::Transcript;
use ssgkr_primitives::field::ChallengeField;
use ssgkr_sumcheck::{SumcheckError, SumcheckProof};

#[cfg(creusot)]
use creusot_std::prelude::ensures;

/// One layer's contribution to a GKR proof: the sumcheck transcript plus
/// the two claimed evaluations of the next layer's MLE that the sumcheck
/// subclaim is reduced to (standard two-point opening, combined by a
/// verifier challenge before the next layer starts).
///
/// `PartialEq`/`Eq` gated out of the Creusot build (field elements
/// cannot carry `DeepModel`; see `ssgkr_sumcheck::MultilinearPoly`).
#[derive(Clone, Debug)]
#[cfg_attr(not(creusot), derive(PartialEq, Eq))]
pub struct LayerProof {
    /// Sumcheck messages for this layer's wiring identity.
    pub sumcheck: SumcheckProof<ChallengeField>,
    /// Claimed `V_{i+1}(x*)`.
    pub eval_x: ChallengeField,
    /// Claimed `V_{i+1}(y*)`.
    pub eval_y: ChallengeField,
}

/// GKR proof: one [`LayerProof`] per circuit layer, output layer first.
///
/// `PartialEq`/`Eq` gated out of the Creusot build (see [`LayerProof`]).
#[derive(Clone, Debug)]
#[cfg_attr(not(creusot), derive(PartialEq, Eq))]
pub struct GkrProof {
    /// Per-layer proofs, in reduction order.
    pub layer_proofs: Vec<LayerProof>,
}

/// The residual claims a successful verification leaves behind: the INPUT
/// vector's multilinear extension must take the claimed values at the two
/// random points the final layer reduces to (`x*` and `y*` of the last
/// sumcheck). The caller (who knows/commits to the inputs) discharges both;
/// for the SMT workload that caller is the composed prover in the root
/// crate (internal-verifier model, seal S-4).
///
/// Two points are always present: general GKR layers carry both the `x*`
/// and `y*` evaluations forward for binary (`Mul`) gates. For the SMT
/// workload the input-adjacent layer is affine (`Mul`-free), so `y*` is
/// redundant but still checked (it costs one extra MLE evaluation and keeps
/// the core general and uniform).
///
/// `PartialEq`/`Eq` gated out of the Creusot build (see [`LayerProof`]).
#[derive(Clone, Debug)]
#[cfg_attr(not(creusot), derive(PartialEq, Eq))]
pub struct InputClaim {
    /// Primary residual point `x*`.
    pub point: Vec<ChallengeField>,
    /// Required input MLE evaluation at `point`.
    pub expected_eval: ChallengeField,
    /// Second residual point `y*`.
    pub point_y: Vec<ChallengeField>,
    /// Required input MLE evaluation at `point_y`.
    pub expected_eval_y: ChallengeField,
}

/// GKR verifier rejection reasons.
#[derive(Clone, Debug)]
pub enum GkrError {
    /// A layer's sumcheck failed.
    Sumcheck {
        /// Layer index (0 = output layer).
        layer: usize,
        /// Underlying sumcheck error.
        source: SumcheckError,
    },
    /// The reduced claim did not match the layer identity at the sampled
    /// point (wiring/opening mismatch).
    LayerClaimMismatch {
        /// Layer index.
        layer: usize,
    },
    /// Proof shape does not match the circuit (layer count, widths).
    ShapeMismatch,
}

/// Prove correct evaluation of `circuit` on the witness (all layer
/// values, as produced by [`evaluate_circuit`]).
///
/// The claimed outputs are `witness.layer_values[0]`; the transcript must
/// already have observed the circuit digest, public inputs and claimed
/// outputs (S-5 order is owned by the caller, one level up). The prover
/// builds its sumcheck oracles directly from the circuit gates, so (unlike
/// [`verify`]) it needs no wiring oracle.
///
/// FV-CONTRACT (Creusot, R2/R3 - the witness-shape `requires` and the
/// completeness clause are design contracts, NOT tool-checked; the
/// completeness statement is held by the model
/// (`gkr_layer_reduction_complete`) and the round-trip tests):
///   #[requires(witness.layer_values.len() == circuit.depth() + 1)]
///   #[ensures(completeness: honest witness => verify accepts)]
///
/// The chain-shape clause (one layer proof per circuit layer, the fact
/// `gkr_chain_bad` consumes) is also design-level: it is walled inside
/// `reduce::prove_impl` (see there).
pub fn prove(
    circuit: &LayeredCircuit<ssgkr_primitives::field::BaseField>,
    witness: &CircuitWitness<ssgkr_primitives::field::BaseField>,
    transcript: &mut Transcript,
) -> GkrProof {
    reduce::prove(circuit, witness, transcript)
}

/// Verify a GKR proof against the circuit structure, the wiring oracle and
/// the claimed output values (already absorbed into the transcript by the
/// caller). Returns the residual [`InputClaim`] on success. The wiring
/// oracle supplies the closed-form predicate/const MLE evaluations at the
/// random points; it MUST describe the same wiring as `circuit`'s gates.
pub fn verify<W: WiringOracle<ChallengeField>>(
    circuit: &LayeredCircuit<ssgkr_primitives::field::BaseField>,
    wiring: &W,
    claimed_outputs: &[ssgkr_primitives::field::BaseField],
    proof: &GkrProof,
    transcript: &mut Transcript,
) -> Result<InputClaim, GkrError> {
    reduce::verify(circuit, wiring, claimed_outputs, proof, transcript)
}
