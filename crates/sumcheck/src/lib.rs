//! Multilinear sumcheck protocol (self-implemented, spec-literal).
//!
//! GENERIC layer: this crate knows nothing about SMTs, circuits, or any
//! StateSync workload, and must stay extractable as a standalone crate.
//! It depends only on the field/transcript adapter (`ssgkr-primitives`).
//!
//! # FV anchoring (Theorem B / refinement R2)
//!
//! The protocol shape refines the AFP entry `Sumcheck_Protocol`
//! (Garvia, Sprenger, Bootle 2024); see
//! `formal/isabelle/GKR_Protocol/Sumcheck_Instance.thy`
//! for the exact mapping. The load-bearing correspondences:
//!
//! - instance = "sum of the oracle polynomial over {0,1}^n equals
//!   `claimed_sum`" ([`SumcheckInstance`]),
//! - per round, the prover sends a bounded-degree univariate
//!   ([`RoundPoly`]); the verifier checks `deg` and
//!   `g(0) + g(1) == previous claim`, then draws a challenge
//!   (AFP `sc_ver1`),
//! - the FINAL oracle evaluation (AFP `sc_ver0`) is NOT performed here:
//!   [`verify`] returns a [`Subclaim`] and the CALLER (GKR layer
//!   reduction, or a direct evaluation at the input layer) discharges it.
//!   This split is the frozen interface S-2.
//!
//! SEAL[S-2]: `SumcheckInstance`, `SumcheckOracle`, `Subclaim` and the
//! round message order are frozen at G1. Changing them invalidates the
//! Isabelle correspondence and is never an inline decision.

// Creusot-only (R2): `extern_spec!` for `Vec` methods must repeat the std
// signature, which names the unstable `Allocator` param. Gated so normal
// (stable) builds never see the feature attribute.
#![cfg_attr(creusot, feature(allocator_api))]

pub mod poly;

pub use poly::{MultilinearPoly, PolyError, RoundPoly};

use ssgkr_primitives::Transcript;
use ssgkr_primitives::field::{ChallengeField, Field};

#[cfg(creusot)]
use creusot_std::prelude::{Int, ensures, inv, invariant, logic, requires, snapshot, trusted};

/// Public statement of one sumcheck run.
///
/// `PartialEq`/`Eq` gated out of the Creusot build (generic `F` cannot
/// carry `DeepModel` - see `poly::MultilinearPoly`).
#[derive(Clone, Copy, Debug)]
#[cfg_attr(not(creusot), derive(PartialEq, Eq))]
pub struct SumcheckInstance<F> {
    /// Number of variables (= number of rounds).
    pub num_vars: usize,
    /// Per-round univariate degree bound (AFP `deg` check).
    pub degree_bound: usize,
    /// Claimed sum over the boolean hypercube.
    pub claimed_sum: F,
}

/// Prover-side oracle for the polynomial being summed.
///
/// One implementor per workload (e.g. the GKR layer reduction implements
/// this for its wiring identity). The oracle owns all polynomial state;
/// the protocol driver below owns only message ordering.
///
/// AFP refinement map: `round_poly` ~ honest prover message,
/// `bind` ~ `inst` on the current variable.
pub trait SumcheckOracle<F: Field> {
    /// Logical view of the remaining variable count (verification builds
    /// only). S-2 seal EXTENSION, supervisor/Jay-approved at the 3b
    /// refinement close-out (refinement_status 16.7 decision 2, executed
    /// in section 17): a `cfg(creusot)` contract-only member, so the
    /// production trait surface - what S-2 freezes - is unchanged (normal
    /// builds never see it). It exists so the contracts below can NAME
    /// the oracle's variable count at the interface, which is where the
    /// AFP correspondence lives.
    #[cfg(creusot)]
    #[logic]
    fn n_vars(self) -> Int;

    /// Remaining number of variables.
    #[cfg_attr(creusot, ensures(result@ == self.n_vars()))]
    fn num_vars(&self) -> usize;

    /// Degree bound of every round polynomial.
    fn degree_bound(&self) -> usize;

    /// The univariate `g_j(X) = sum over remaining vars of the oracle
    /// polynomial with the current variable left free`.
    fn round_poly(&self) -> RoundPoly<F>;

    /// Bind the current variable to challenge `r` (arity - 1).
    ///
    /// R2 contract (Creusot, ACTIVE - the former design contract of this
    /// method, machine-stated via the [`Self::n_vars`] view): binding
    /// consumes exactly one variable. This is the Rust mirror of the AFP
    /// round step the model consumes per round (`inst` on the current
    /// variable: each `Sumcheck_Protocol.sumcheck` round retires one
    /// `(variable, challenge)` pair; `gkr_layer_sumcheck` locale,
    /// Sumcheck_Instance.thy). Consumed by [`prove`]'s loop invariant;
    /// machine-checked at the implementor (`SparseLayerOracle`,
    /// reduce.rs) on the non-phase-boundary paths - the boundary path
    /// threads a helper whose monolithic vc is wall-pinned (see
    /// `build_phase2`'s TOOL WALL note there).
    #[cfg_attr(creusot, requires((*self).n_vars() > 0))]
    #[cfg_attr(creusot, ensures((^self).n_vars() == (*self).n_vars() - 1))]
    fn bind(&mut self, r: F);
}

/// Where challenges come from. Implemented for the Fiat-Shamir
/// [`Transcript`] below; test code may implement it with fixed vectors.
pub trait ChallengeSource<F> {
    /// Absorb a round polynomial (coefficient order) into the transcript.
    fn observe_round_poly(&mut self, poly: &RoundPoly<F>);
    /// Draw the next challenge.
    fn draw_challenge(&mut self) -> F;
}

impl ChallengeSource<ChallengeField> for Transcript {
    fn observe_round_poly(&mut self, poly: &RoundPoly<ChallengeField>) {
        for c in poly.coeffs() {
            self.observe_ext(*c);
        }
    }

    fn draw_challenge(&mut self) -> ChallengeField {
        self.sample_challenge()
    }
}

/// Non-interactive sumcheck proof: the round polynomials in round order.
///
/// `PartialEq`/`Eq` gated out of the Creusot build (generic `F`).
#[derive(Clone, Debug)]
#[cfg_attr(not(creusot), derive(PartialEq, Eq))]
pub struct SumcheckProof<F> {
    /// `g_0, g_1, ..., g_{n-1}`.
    pub round_polys: Vec<RoundPoly<F>>,
}

/// What remains after all rounds: "the oracle polynomial evaluates to
/// `expected_eval` at `point`". Discharged by the caller (S-2).
///
/// `PartialEq`/`Eq` gated out of the Creusot build (generic `F`).
#[derive(Clone, Debug)]
#[cfg_attr(not(creusot), derive(PartialEq, Eq))]
pub struct Subclaim<F> {
    /// The random point accumulated over the rounds.
    pub point: Vec<F>,
    /// Required oracle evaluation at `point`.
    pub expected_eval: F,
}

/// Verifier-side rejection reasons.
///
/// `PartialEq`/`Eq` gated out of the Creusot build (no contract consumes
/// error equality; see `poly::PolyError`).
#[derive(Clone, Debug)]
#[cfg_attr(not(creusot), derive(PartialEq, Eq))]
pub enum SumcheckError {
    /// Round polynomial exceeds the degree bound (AFP deg check).
    DegreeExceeded {
        /// Failing round index.
        round: usize,
    },
    /// `g(0) + g(1)` does not match the running claim (AFP sum check).
    SumMismatch {
        /// Failing round index.
        round: usize,
    },
    /// Proof has a different number of rounds than the instance.
    WrongRoundCount {
        /// Rounds expected (= `num_vars`).
        expected: usize,
        /// Rounds found in the proof.
        found: usize,
    },
}

/// Run the prover side: drive the oracle through all rounds against a
/// challenge source, producing the proof and the prover-side subclaim
/// (useful for self-checks and for the GKR chain).
///
/// FV-CONTRACT (Creusot, R2 - design contract, NOT tool-checked):
///   #[requires(oracle.num_vars() > 0)]
///   #[ensures(result.0.round_polys.len() == old(oracle.num_vars()))]
///   #[ensures(result.1.point.len() == old(oracle.num_vars()))]
/// TOOL WALL update (S-2 seal-extension session, refinement_status
/// section 17): the [`SumcheckOracle::n_vars`] logic view now exists, so
/// the len clauses are no longer tool-blocked; their activation is
/// mapping-#15 contract work, outside that session's #14 mandate. They
/// stay design contracts held by the model side. What the loop DOES
/// machine-check now is the bind arity law: the invariant below threads
/// `n_vars = rounds - #produced`, which both discharges `bind`'s
/// precondition and consumes its arity postcondition every round.
/// (R2 audit update: the body's former residual goal -
/// `inv(last_eval)` rooted in the foreign constant `F::ZERO`, the
/// generic-inv face of R1 wall 4 layer 3 - is discharged by the
/// [`poly::foreign_zero_wf`] bridge axiom plus the `inv(last_eval)`
/// loop invariant; the body is now fully machine-checked.)
///
/// FV-KANI (R2, sketch): for num_vars <= 3 over a toy field, prove that
/// an honest oracle always yields a proof accepted by [`verify`] with the
/// same challenge source (completeness harness).
pub fn prove<F, O, C>(oracle: &mut O, challenges: &mut C) -> (SumcheckProof<F>, Subclaim<F>)
where
    F: Field,
    O: SumcheckOracle<F>,
    C: ChallengeSource<F>,
{
    let rounds = oracle.num_vars();
    let mut round_polys = Vec::with_capacity(rounds);
    let mut point = Vec::with_capacity(rounds);
    let mut last_eval = F::ZERO;

    #[cfg_attr(creusot, invariant(poly::foreign_zero_wf::<F>()))]
    #[cfg_attr(creusot, invariant(inv(last_eval)))]
    #[cfg_attr(creusot, invariant((*oracle).n_vars() == rounds@ - produced.len()))]
    for _ in 0..rounds {
        let g = oracle.round_poly();
        challenges.observe_round_poly(&g);
        let r = challenges.draw_challenge();
        last_eval = g.eval_at(r);
        oracle.bind(r);
        point.push(r);
        round_polys.push(g);
    }

    (
        SumcheckProof { round_polys },
        Subclaim {
            point,
            expected_eval: last_eval,
        },
    )
}

/// Run the verifier side. Performs the AFP `sc_ver1` checks per round
/// (degree bound, `g(0) + g(1) == claim`) and returns the final
/// [`Subclaim`]; the caller discharges the oracle evaluation (AFP
/// `sc_ver0` equivalent).
///
/// This function IS the soundness semantics of the protocol driver; its
/// body is spec-literal on purpose and must stay boring.
///
/// FV-CONTRACT (Creusot, R2 - design contract, NOT tool-checked):
///   #[ensures(Ok(sc) ==> proof.round_polys.len() == instance.num_vars
///       && sc.point.len() == instance.num_vars
///       && every round poly's degree <= instance.degree_bound)]
/// TOOL WALL (R2 dev, narrowed by the verifier-acceptance strengthening):
/// foreign-field equality cannot carry `DeepModel`, so only
/// [`running_claim_matches`] remains a claim-free `trusted` computation
/// seam. The round-count, degree, rejection, transcript-order, and point
/// accumulation control flow below is translated normally. The AFP-side
/// meaning remains in `layer_sumcheck_soundness`.
pub fn verify<F, C>(
    instance: &SumcheckInstance<F>,
    proof: &SumcheckProof<F>,
    challenges: &mut C,
) -> Result<Subclaim<F>, SumcheckError>
where
    F: Field,
    C: ChallengeSource<F>,
{
    if proof.round_polys.len() != instance.num_vars {
        return Err(SumcheckError::WrongRoundCount {
            expected: instance.num_vars,
            found: proof.round_polys.len(),
        });
    }

    let mut claim = instance.claimed_sum;
    let mut point = Vec::with_capacity(instance.num_vars);

    for g in proof.round_polys.iter() {
        let round = point.len();
        if g.degree() > instance.degree_bound {
            return Err(SumcheckError::DegreeExceeded { round });
        }
        if !running_claim_matches(g, claim) {
            return Err(SumcheckError::SumMismatch { round });
        }
        challenges.observe_round_poly(g);
        let r = challenges.draw_challenge();
        claim = g.eval_at(r);
        point.push(r);
    }

    Ok(Subclaim {
        point,
        expected_eval: claim,
    })
}

/// The one foreign-field equality in [`verify`].
///
/// This is a claim-free translation opt-out: it adds no equality axiom or
/// postcondition. Creusot treats the Boolean result as an arbitrary observed
/// check value, while the non-trusted outer verifier proves that `Ok` is
/// reachable only through its `true` branch.
#[cfg_attr(creusot, trusted)]
fn running_claim_matches<F: Field>(g: &RoundPoly<F>, claim: F) -> bool {
    g.eval_at(F::ZERO) + g.eval_at(F::ONE) == claim
}
