//! GKR layer-reduction prover and verifier (the core of Theorem B).
//!
//! # The layer identity being proved (S-3 amended algebra)
//!
//! For each layer `i`, with `V_i` the multilinear extension of that layer's
//! values and `V = V_{i+1}` the layer below (`s = in_width_bits` variables):
//!
//! ```text
//! V_i(z) = const~(z)
//!        + sum_x    lin~(z,x)   * V(x)
//!        + sum_{x,y} mul~(z,x,y) * V(x) * V(y)
//!        + sum_x    pow3~(z,x)  * V(x)^3
//! ```
//!
//! # One sumcheck per layer
//!
//! A claim `V_i(z_k) = t_k` (one point for the output layer, two thereafter,
//! combined with verifier coefficients `c_k`) is reduced to claims about
//! `V_{i+1}` by a single sumcheck over `2s` variables `(x, y)` of
//!
//! ```text
//! P(x,y) = sum_k c_k [ lin~(z_k,x) V(x) beta(y)
//!                    + mul~(z_k,x,y) V(x) V(y)
//!                    + pow3~(z_k,x) V(x)^3 beta(y) ]
//! ```
//!
//! where `beta(y) = prod_j (1 - y_j)` lifts the unary terms onto the `(x,y)`
//! hypercube (`sum_y beta(y) = 1`). Summed over the hypercube this equals
//! `sum_k c_k (V_i(z_k) - const~(z_k))`. Per-round degree is `<= 4` (the
//! `pow3` term is `deg-1 predicate * deg-3 cube` in an x-variable; every
//! factor that does not depend on the current variable is constant in it,
//! so the y-rounds are `deg <= 2`). This degree-4 round polynomial is
//! distinct from the layer's algebraic degree (`<= 3`, the `x^3` gate).
//!
//! After the sumcheck the residual `V_{i+1}` evaluations at the two random
//! points `x*, y*` (`eval_x`, `eval_y` in [`crate::LayerProof`]) become the
//! next layer's claims, combined with a fresh Fiat-Shamir challenge
//! `(1, r)`. At the input layer they are returned as the [`crate::InputClaim`]
//! for the caller to discharge (internal-verifier model, seal S-4).

use ssgkr_primitives::Transcript;
use ssgkr_primitives::field::{ChallengeField, Field, PrimeCharacteristicRing};
use ssgkr_sumcheck::{RoundPoly, SumcheckInstance, SumcheckOracle};

use crate::circuit::{CircuitWitness, GateKind, Layer, LayeredCircuit};
use crate::mle::{cf_u64, embed, eq_point_index, mle_eval_base};
use crate::wiring::WiringOracle;
use crate::{GkrError, GkrProof, InputClaim, LayerProof};

use ssgkr_primitives::field::BaseField;

#[cfg(creusot)]
use creusot_std::prelude::{Int, ensures, extern_spec, logic, pearlite, requires, trusted};

// `slice::split_at` / `slice::to_vec` std facts (creusot-std gap; same
// class as the R1 `div_ceil` spec): prefix/suffix split and verbatim
// copy. Needed by the layer loop's `subclaim.point.split_at(s_in)`.
#[cfg(creusot)]
extern_spec! {
    impl<T> [T] {
        #[requires(mid@ <= self@.len())]
        #[ensures(result.0@.len() == mid@ && result.1@.len() == self@.len() - mid@)]
        #[ensures(forall<i: Int> 0 <= i && i < mid@ ==> result.0@[i] == self@[i])]
        #[ensures(forall<i: Int> 0 <= i && i < result.1@.len() ==> result.1@[i] == self@[mid@ + i])]
        fn split_at(&self, mid: usize) -> (&[T], &[T]);
    }
}

/// Per-round univariate degree bound of the layer sumcheck (see module docs:
/// the `pow3` term is degree 4 in an x-variable).
pub const LAYER_ROUND_DEGREE: usize = 4;

/// `beta(point) = prod_j (1 - point_j)` = the multilinear extension of the
/// "all-zero" indicator, evaluated at `point`.
fn beta_eval(point: &[ChallengeField]) -> ChallengeField {
    point.iter().fold(ChallengeField::ONE, |acc, &p| {
        acc * (ChallengeField::ONE - p)
    })
}

/// Lagrange interpolation of `values` at `nodes` into ascending coefficients.
/// `nodes` must be distinct. Returns a coefficient vector of length
/// `nodes.len()` (trailing zeros left in place; the degree bound is enforced
/// by the verifier).
///
/// The `try_inverse` below is over `nodes[k] - nodes[j]` with `j != k`; the
/// nodes are the fixed distinct constants `{0, 1, 2, 3, 4}`, so the
/// difference is always a nonzero small integer (invertible in the field).
/// A `None` here would be an internal invariant violation, not a runtime
/// error path.
#[allow(clippy::expect_used)]
fn lagrange_interpolate(
    nodes: &[ChallengeField],
    values: &[ChallengeField],
) -> Vec<ChallengeField> {
    let n = nodes.len();
    let mut coeffs = vec![ChallengeField::ZERO; n];
    for k in 0..n {
        let mut denom = ChallengeField::ONE;
        for (j, &nj) in nodes.iter().enumerate() {
            if j != k {
                denom *= nodes[k] - nj;
            }
        }
        let scale = values[k]
            * denom
                .try_inverse()
                .expect("interpolation nodes are distinct");
        // basis(X) = prod_{j != k} (X - nodes[j]), ascending coeffs.
        let mut basis = vec![ChallengeField::ONE];
        for (j, &nj) in nodes.iter().enumerate() {
            if j == k {
                continue;
            }
            // multiply basis by (X - nj)
            let mut next = vec![ChallengeField::ZERO; basis.len() + 1];
            for (i, &b) in basis.iter().enumerate() {
                next[i + 1] += b; // X * b
                next[i] -= nj * b; // -nj * b
            }
            basis = next;
        }
        for (i, &b) in basis.iter().enumerate() {
            coeffs[i] += scale * b;
        }
    }
    coeffs
}

/// Multilinear extrapolation of a folded table entry to node `x`:
/// `t(x) = t[i] + x * (t[i+half] - t[i])` (the current variable is the MSB).
#[inline]
fn extrap(t: &[ChallengeField], i: usize, half: usize, x: ChallengeField) -> ChallengeField {
    t[i] + x * (t[i + half] - t[i])
}

/// Prover-side sumcheck oracle for one layer reduction, using Libra-style
/// two-phase sparse booking. This is the production oracle (the N3
/// optimization of the v0.1 dense oracle, D-33 (8)); it stays
/// observationally equal to [`DenseLayerOracle`] (the test-only reference)
/// - every round emits a bit-identical [`RoundPoly`].
///
/// # Why this equals the dense oracle
///
/// The dense oracle materializes six `2^{2s}` factor tables over the full
/// `(x, y)` hypercube and, each round, sums
/// `lin*vx*beta + mul*vx*vy + pow*vx^3*beta` over the remaining cube. Three
/// of those tables (`lin`, `pow`, `vx`) depend only on `x`, two (`vy`,
/// `beta`) only on `y`, and `mul` is `#gates`-sparse. Splitting
/// `sum_{x,y}` into `sum_x sum_y` collapses the inner `y` sum in closed
/// form, which is what makes the sparse node values *equal* the dense ones
/// (the regrouping uses only field distributivity/commutativity, exact in
/// a finite field, so the results are bit-identical, hence the interpolated
/// coefficient vectors - trailing zeros included - are identical):
///
/// - `beta(y) = [y == 0]`, so `sum_y beta(y) = 1`: the `lin` and `pow`
///   terms lose their `y` sum entirely (they become `x`-only).
/// - the `mul` term factors as `vx(x) * (sum_y mul(x,y) * vy(y))`; the
///   inner `y` sum is precomputed into a booking table
///   `amul(x) = sum_y mul(x,y) * vy(y)`, built in `O(#Mul)` from the gate
///   list.
///
/// So while `x` is bound (Phase 1) the oracle keeps only four `2^s`-sized
/// `x`-tables (`lin_x`, `pow_x`, `vx`, `amul_x`) and each round evaluates
/// `lin*vx + amul*vx + pow*vx^3` over the remaining `x`-cube. Once `x` is
/// fully bound at `x*` (Phase 2) the `x`-only factors are the scalars
/// `L* = lin~(x*)`, `P* = pow3~(x*)`, `V* = V(x*)`, and the sum runs over
/// `y`: `(L*V* + P*V*^3)*beta(y) + V* * mulx(y) * vy(y)`, where
/// `mulx(y) = sum_k c_k mul~(z_k, x*, y) = sum_{Mul gates} weight *
/// eq(x*, in1)` accumulated at `in2` (built in `O(#Mul * s)` at the phase
/// transition). This is exactly the polynomial the dense oracle sums in
/// its second `s` rounds.
///
/// # Complexity
///
/// Build `O(#gates + 2^s)`; per round `O(2^{remaining})` over a single
/// `s`-bit cube. No `2^{2s}` allocation anywhere; peak memory
/// `O(2^s + #Mul)` (vs the dense `O(2^{2s})`).
struct SparseLayerOracle {
    /// `s_in`: the `x` and `y` blocks are each `s` bits (total `2s` vars).
    s: usize,
    /// Variables not yet bound (starts at `2s`; Phase 1 while `> s`).
    remaining: usize,
    // --- Phase 1 tables (x-block), size `2^(remaining - s)` while binding x.
    /// `sum_k c_k lin~(z_k, x)` over the current x-cube.
    lin_x: Vec<ChallengeField>,
    /// `sum_k c_k pow3~(z_k, x)` over the current x-cube.
    pow_x: Vec<ChallengeField>,
    /// `V(x)` over the current x-cube.
    vx: Vec<ChallengeField>,
    /// Booking table `amul(x) = sum_y mul~(z,x,y) * V(y)` over the current
    /// x-cube (the `mul` term's y-sum, precomputed and folded in x).
    amul_x: Vec<ChallengeField>,
    // --- retained from construction, consumed at the Phase-2 build.
    /// Sparse `Mul` gates `(in1, in2, weight = coeff * w[out])`.
    mul_gates: Vec<(u32, u32, ChallengeField)>,
    /// `V` (layer-below MLE) embedded, size `2^s`; becomes `vy` at the
    /// phase transition.
    v_embed: Vec<ChallengeField>,
    /// The x-challenges accumulated during Phase 1 (= `x*` once complete).
    xstar: Vec<ChallengeField>,
    // --- Phase 2 tables (y-block), size `2^remaining` while binding y.
    /// `beta(y)` = all-zero indicator over the current y-cube.
    beta_y: Vec<ChallengeField>,
    /// `V(y)` over the current y-cube.
    vy: Vec<ChallengeField>,
    /// `mulx(y) = sum_k c_k mul~(z_k, x*, y)` over the current y-cube.
    mulx_y: Vec<ChallengeField>,
    /// `L* = sum_k c_k lin~(z_k, x*)` (Phase 2 scalar).
    lstar: ChallengeField,
    /// `P* = sum_k c_k pow3~(z_k, x*)` (Phase 2 scalar).
    pstar: ChallengeField,
    /// `V* = V(x*)` (Phase 2 scalar).
    vstar: ChallengeField,
}

impl SparseLayerOracle {
    /// Build the oracle for layer `i` from its gates, the incoming claim
    /// points, and the layer-below values. Same signature as
    /// [`DenseLayerOracle::new`] so the two share one prover driver.
    fn new(
        layer: &Layer<BaseField>,
        s_in: usize,
        incoming: &[(Vec<ChallengeField>, ChallengeField)],
        v_below: &[BaseField],
    ) -> Self {
        let s_out = layer.width_bits;
        let out_len = 1usize << s_out;
        let in_len = 1usize << s_in;

        // w[o] = sum_k c_k eq(z_k, o): fold the incoming points into a weight
        // per output wire so the gate loop stays a single pass. (Identical
        // to the dense oracle.)
        let mut w = vec![ChallengeField::ZERO; out_len];
        for (z, c) in incoming {
            for (o, wo) in w.iter_mut().enumerate() {
                *wo += *c * eq_point_index(z, o);
            }
        }

        // Per-kind weights. Lin/Pow3 collapse onto an x-table; Mul stays a
        // gate list and is NEVER expanded into a 2^{2s} table.
        let mut lin_x = vec![ChallengeField::ZERO; in_len];
        let mut pow_x = vec![ChallengeField::ZERO; in_len];
        let mut mul_gates: Vec<(u32, u32, ChallengeField)> = Vec::new();
        for g in &layer.gates {
            let weight = embed(g.coeff) * w[g.out as usize];
            match g.kind {
                GateKind::Lin => lin_x[g.in1 as usize] += weight,
                GateKind::Pow3 => pow_x[g.in1 as usize] += weight,
                GateKind::Mul => mul_gates.push((g.in1, g.in2, weight)),
            }
        }

        // V embedded over the input block (indexed the same way the dense
        // oracle indexes both `vx[x]` and `vy[y]`).
        let v_embed: Vec<ChallengeField> = (0..in_len).map(|x| embed(v_below[x])).collect();

        // Booking table amul(x) = sum_y mul(x,y) * V(y), accumulated from the
        // sparse Mul list in O(#Mul). Duplicate (in1, in2) gates simply add.
        let mut amul_x = vec![ChallengeField::ZERO; in_len];
        for &(in1, in2, weight) in &mul_gates {
            amul_x[in1 as usize] += weight * v_embed[in2 as usize];
        }

        let vx = v_embed.clone();
        Self {
            s: s_in,
            remaining: 2 * s_in,
            lin_x,
            pow_x,
            vx,
            amul_x,
            mul_gates,
            v_embed,
            xstar: Vec::with_capacity(s_in),
            beta_y: Vec::new(),
            vy: Vec::new(),
            mulx_y: Vec::new(),
            lstar: ChallengeField::ZERO,
            pstar: ChallengeField::ZERO,
            vstar: ChallengeField::ZERO,
        }
    }

    /// At the Phase 1 -> Phase 2 boundary (`x` fully bound at `x*`, so the
    /// four x-tables are length 1): read the x-only scalars and build the
    /// three y-block tables.
    ///
    /// FV-CONTRACT (Creusot, seal-extension session - design contract,
    /// NOT tool-checked):
    ///   #[ensures((^self).remaining@ == (*self).remaining@)]
    /// TOOL WALL (honest carry-over; refinement_status section 17): the
    /// counter-preservation ensures cannot be activated at this rev -
    /// this body's vc is a monolithic chunk that split_vc cannot
    /// decompose (depth 16 probed), and once the `vec![ZERO; _]` calls
    /// enter it the solvers diverge (all-timeout, R1 wall-2
    /// phenomenology). A full activation attempt (six machine-width /
    /// call-domain `requires` including the model's `gates_in` mirror, a
    /// claim-free `AddAssign` spec, bridge-axiom references) was measured
    /// no-score and reverted. The preservation clause itself IS
    /// machine-provable: the scalars + shift + `mem::take` prefix variant
    /// proved green with the ensures active - the blocker is the
    /// monolith, not the semantics. Consequence: `bind`'s arity
    /// postcondition is machine-checked on the non-boundary paths and
    /// stays a wall-pinned open subgoal on the phase-boundary path
    /// (where this helper's frame havocs the counter).
    fn build_phase2(&mut self) {
        self.vstar = self.vx[0];
        self.lstar = self.lin_x[0];
        self.pstar = self.pow_x[0];

        let in_len = 1usize << self.s;
        let mut beta_y = vec![ChallengeField::ZERO; in_len];
        beta_y[0] = ChallengeField::ONE;
        self.beta_y = beta_y;

        // vy = V over the y-block (the still-full embedded layer-below values).
        self.vy = std::mem::take(&mut self.v_embed);

        // mulx(y) = sum_k c_k mul~(z_k, x*, y) = sum_{Mul gates} weight *
        // eq(x*, in1), accumulated at in2. O(#Mul * s).
        let mut mulx_y = vec![ChallengeField::ZERO; in_len];
        for &(in1, in2, weight) in &self.mul_gates {
            mulx_y[in2 as usize] += weight * eq_point_index(&self.xstar, in1 as usize);
        }
        self.mulx_y = mulx_y;
    }
}

impl SumcheckOracle<ChallengeField> for SparseLayerOracle {
    /// Logical view of `remaining` (S-2 seal extension - see the trait).
    #[cfg(creusot)]
    #[logic]
    fn n_vars(self) -> Int {
        pearlite! { self.remaining@ }
    }

    // Trait contracts are restated verbatim on the impl methods below:
    // this toolchain rev does not inherit trait contracts into impls
    // (an uncontracted impl gets the trivial contract and the refines
    // check then fails) - same convention as the R1 `HashGadget` /
    // `Poseidon2Gadget` restatement.
    #[cfg_attr(creusot, ensures(result@ == self.n_vars()))]
    fn num_vars(&self) -> usize {
        self.remaining
    }

    fn degree_bound(&self) -> usize {
        LAYER_ROUND_DEGREE
    }

    fn round_poly(&self) -> RoundPoly<ChallengeField> {
        let nodes = [cf_u64(0), cf_u64(1), cf_u64(2), cf_u64(3), cf_u64(4)];
        let mut vals = [ChallengeField::ZERO; 5];
        if self.remaining > self.s {
            // Phase 1 (x-round): the y sum is already collapsed - beta -> 1
            // (dropped from lin/pow) and mul -> amul.
            let len = 1usize << (self.remaining - self.s);
            let half = len / 2;
            for (ni, &t) in nodes.iter().enumerate() {
                let mut acc = ChallengeField::ZERO;
                for i in 0..half {
                    let lin = extrap(&self.lin_x, i, half, t);
                    let pow = extrap(&self.pow_x, i, half, t);
                    let vx = extrap(&self.vx, i, half, t);
                    let amul = extrap(&self.amul_x, i, half, t);
                    acc += lin * vx + amul * vx + pow * vx * vx * vx;
                }
                vals[ni] = acc;
            }
        } else {
            // Phase 2 (y-round): x is fixed at x*, so the x-only factors are
            // the scalars L*, P*, V*. `c_beta` groups the two beta terms
            // exactly as the dense oracle sums `lin*vx*beta + pow*vx^3*beta`.
            let len = 1usize << self.remaining;
            let half = len / 2;
            let c_beta =
                self.lstar * self.vstar + self.pstar * self.vstar * self.vstar * self.vstar;
            for (ni, &t) in nodes.iter().enumerate() {
                let mut acc = ChallengeField::ZERO;
                for i in 0..half {
                    let beta = extrap(&self.beta_y, i, half, t);
                    let mul = extrap(&self.mulx_y, i, half, t);
                    let vy = extrap(&self.vy, i, half, t);
                    acc += c_beta * beta + self.vstar * mul * vy;
                }
                vals[ni] = acc;
            }
        }
        RoundPoly::from_coeffs(lagrange_interpolate(&nodes, &vals))
    }

    #[cfg_attr(creusot, requires((*self).n_vars() > 0))]
    #[cfg_attr(creusot, ensures((^self).n_vars() == (*self).n_vars() - 1))]
    fn bind(&mut self, r: ChallengeField) {
        if self.remaining > self.s {
            // Phase 1: fold the top x-variable of the four x-tables; record
            // the challenge; build the y-tables once x is complete.
            let len = 1usize << (self.remaining - self.s);
            let half = len / 2;
            for t in [
                &mut self.lin_x,
                &mut self.pow_x,
                &mut self.vx,
                &mut self.amul_x,
            ] {
                for i in 0..half {
                    t[i] = t[i] + r * (t[i + half] - t[i]);
                }
                t.truncate(half);
            }
            self.xstar.push(r);
            self.remaining -= 1;
            if self.remaining == self.s {
                self.build_phase2();
            }
        } else {
            // Phase 2: fold the top y-variable of the three y-tables.
            let len = 1usize << self.remaining;
            let half = len / 2;
            for t in [&mut self.beta_y, &mut self.vy, &mut self.mulx_y] {
                for i in 0..half {
                    t[i] = t[i] + r * (t[i + half] - t[i]);
                }
                t.truncate(half);
            }
            self.remaining -= 1;
        }
    }
}

/// Test-only dense reference oracle: materializes the six `2^{2s}` factor
/// tables over the `(x, y)` hypercube and folds the current MSB variable of
/// all of them each round. This is the semantic anchor (D-33 (8)) the
/// production [`SparseLayerOracle`] is proven observationally equal to; it
/// is retained solely to drive the equivalence tests.
#[cfg(test)]
struct DenseLayerOracle {
    /// `sum_k c_k lin~(z_k, x)` as a table over `x` (redundant over `y`).
    lin: Vec<ChallengeField>,
    /// `sum_k c_k pow3~(z_k, x)` as a table over `x` (redundant over `y`).
    pow: Vec<ChallengeField>,
    /// `V(x)` (layer-below MLE, indexed by the x-block).
    vx: Vec<ChallengeField>,
    /// `V(y)` (same values, indexed by the y-block).
    vy: Vec<ChallengeField>,
    /// `beta(y)` = all-zero indicator over the y-block.
    beta: Vec<ChallengeField>,
    /// `sum_k c_k mul~(z_k, x, y)` over `(x, y)`.
    mul: Vec<ChallengeField>,
    /// Number of variables not yet bound.
    remaining: usize,
}

#[cfg(test)]
impl DenseLayerOracle {
    /// Build the dense oracle (same signature as [`SparseLayerOracle::new`]).
    fn new(
        layer: &Layer<BaseField>,
        s_in: usize,
        incoming: &[(Vec<ChallengeField>, ChallengeField)],
        v_below: &[BaseField],
    ) -> Self {
        let s_out = layer.width_bits;
        let out_len = 1usize << s_out;
        let in_len = 1usize << s_in;

        // w[o] = sum_k c_k eq(z_k, o): fold the incoming points into a weight
        // per output wire so the gate loop stays a single pass.
        let mut w = vec![ChallengeField::ZERO; out_len];
        for (z, c) in incoming {
            for (o, wo) in w.iter_mut().enumerate() {
                *wo += *c * eq_point_index(z, o);
            }
        }

        // Sparse per-kind predicate tables (F-valued: gate coeff * w[out]).
        let mut lin_x = vec![ChallengeField::ZERO; in_len];
        let mut pow_x = vec![ChallengeField::ZERO; in_len];
        let mut mul_xy = vec![ChallengeField::ZERO; in_len * in_len];
        for g in &layer.gates {
            let weight = embed(g.coeff) * w[g.out as usize];
            match g.kind {
                GateKind::Lin => lin_x[g.in1 as usize] += weight,
                GateKind::Pow3 => pow_x[g.in1 as usize] += weight,
                GateKind::Mul => mul_xy[(g.in1 as usize) * in_len + g.in2 as usize] += weight,
            }
        }

        let n = 2 * s_in;
        let full = 1usize << n;
        let mut lin = vec![ChallengeField::ZERO; full];
        let mut pow = vec![ChallengeField::ZERO; full];
        let mut vx = vec![ChallengeField::ZERO; full];
        let mut vy = vec![ChallengeField::ZERO; full];
        let mut beta = vec![ChallengeField::ZERO; full];
        let mut mul = vec![ChallengeField::ZERO; full];
        for idx in 0..full {
            let x = idx >> s_in; // high s_in bits (x is the MSB block)
            let y = idx & (in_len - 1); // low s_in bits
            lin[idx] = lin_x[x];
            pow[idx] = pow_x[x];
            vx[idx] = embed(v_below[x]);
            vy[idx] = embed(v_below[y]);
            beta[idx] = if y == 0 {
                ChallengeField::ONE
            } else {
                ChallengeField::ZERO
            };
            mul[idx] = mul_xy[x * in_len + y];
        }

        Self {
            lin,
            pow,
            vx,
            vy,
            beta,
            mul,
            remaining: n,
        }
    }
}

#[cfg(test)]
impl SumcheckOracle<ChallengeField> for DenseLayerOracle {
    fn num_vars(&self) -> usize {
        self.remaining
    }

    fn degree_bound(&self) -> usize {
        LAYER_ROUND_DEGREE
    }

    fn round_poly(&self) -> RoundPoly<ChallengeField> {
        let len = 1usize << self.remaining;
        let half = len / 2;
        let nodes = [cf_u64(0), cf_u64(1), cf_u64(2), cf_u64(3), cf_u64(4)];
        let mut vals = [ChallengeField::ZERO; 5];
        for (ni, &x) in nodes.iter().enumerate() {
            let mut acc = ChallengeField::ZERO;
            for i in 0..half {
                let lin = extrap(&self.lin, i, half, x);
                let pow = extrap(&self.pow, i, half, x);
                let vx = extrap(&self.vx, i, half, x);
                let vy = extrap(&self.vy, i, half, x);
                let beta = extrap(&self.beta, i, half, x);
                let mul = extrap(&self.mul, i, half, x);
                acc += lin * vx * beta + mul * vx * vy + pow * vx * vx * vx * beta;
            }
            vals[ni] = acc;
        }
        RoundPoly::from_coeffs(lagrange_interpolate(&nodes, &vals))
    }

    fn bind(&mut self, r: ChallengeField) {
        let len = 1usize << self.remaining;
        let half = len / 2;
        for t in [
            &mut self.lin,
            &mut self.pow,
            &mut self.vx,
            &mut self.vy,
            &mut self.beta,
            &mut self.mul,
        ] {
            for i in 0..half {
                t[i] = t[i] + r * (t[i + half] - t[i]);
            }
            t.truncate(half);
        }
        self.remaining -= 1;
    }
}

/// Draw `count` Fiat-Shamir challenges from the transcript.
#[cfg_attr(creusot, ensures(result@.len() == count@))]
fn draw_point(transcript: &mut Transcript, count: usize) -> Vec<ChallengeField> {
    (0..count).map(|_| transcript.sample_challenge()).collect()
}

/// Core prover driver, generic over the per-layer oracle constructor so the
/// production ([`SparseLayerOracle`]) and the test-only dense reference
/// ([`DenseLayerOracle`]) share one message-ordering path - which is what
/// makes "same transcript" mechanically guaranteed rather than duplicated.
/// Not public: [`prove`] fixes the sparse oracle.
///
/// FV-CONTRACT (Creusot, R2 - design contract, NOT tool-checked):
///   #[ensures(result.layer_proofs.len() == circuit.layers.len())]
/// (Isabelle: one `LayerProof` per chain position - `gkr_chain_bad`
/// consumes exactly `length Ls` layer messages.)
/// TOOL WALL (R2 dev, honest carry-over): the body seeds the incoming
/// claim with `vec![(z0, ChallengeField::ONE)]` - std `vec!` heap MIR
/// (R1 wall 4, layer 1) with a FOREIGN-CONSTANT argument (`ONE`, wall 4
/// layer 3), so the loop entry sits behind an untranslatable seed
/// either way (the creusot-std `vec!` swap was probed and merely trades
/// the wall for the layer-3 constant obligations). The len clause is
/// therefore stated as documentation; activating it unproved would let
/// callers assume an unverified fact (R1 rule).
fn prove_impl<O, MakeO>(
    circuit: &LayeredCircuit<BaseField>,
    witness: &CircuitWitness<BaseField>,
    transcript: &mut Transcript,
    mut make_oracle: MakeO,
) -> GkrProof
where
    O: SumcheckOracle<ChallengeField>,
    MakeO: FnMut(
        &Layer<BaseField>,
        usize,
        &[(Vec<ChallengeField>, ChallengeField)],
        &[BaseField],
    ) -> O,
{
    let depth = circuit.layers.len();
    let mut layer_proofs = Vec::with_capacity(depth);
    if depth == 0 {
        return GkrProof { layer_proofs };
    }

    // Output-layer claim point z_0 (single incoming point, coefficient 1).
    let z0 = draw_point(transcript, circuit.layers[0].width_bits);
    let mut incoming = vec![(z0, ChallengeField::ONE)];

    for i in 0..depth {
        let layer = &circuit.layers[i];
        let s_in = if i + 1 < depth {
            circuit.layers[i + 1].width_bits
        } else {
            circuit.input_width_bits
        };
        let v_below = &witness.layer_values[i + 1];

        let mut oracle = make_oracle(layer, s_in, &incoming, v_below);
        let (sumcheck, subclaim) = ssgkr_sumcheck::prove(&mut oracle, transcript);

        let (xstar, ystar) = subclaim.point.split_at(s_in);
        let eval_x = mle_eval_base(v_below, xstar);
        let eval_y = mle_eval_base(v_below, ystar);
        transcript.observe_ext(eval_x);
        transcript.observe_ext(eval_y);
        layer_proofs.push(LayerProof {
            sumcheck,
            eval_x,
            eval_y,
        });

        if i + 1 < depth {
            let r = transcript.sample_challenge();
            incoming = vec![(xstar.to_vec(), ChallengeField::ONE), (ystar.to_vec(), r)];
        }
    }

    GkrProof { layer_proofs }
}

/// Prove correct evaluation of `circuit` on `witness` (all layer values).
///
/// The transcript must already have observed the circuit digest, public
/// inputs and claimed outputs (S-5 order, owned by the caller). This
/// function draws the output-layer point and every reduction challenge.
///
/// FV-CONTRACT (Creusot, R2 - design contract, NOT tool-checked; the
/// shape clause is walled inside [`prove_impl`], see there):
///   #[ensures(result.layer_proofs.len() == circuit.layers.len())]
/// Completeness (honest witness => verify accepts) is held by the model
/// (`gkr_layer_reduction_complete` + `layer_sumcheck_completeness`) and
/// the end-to-end round-trip tests.
pub fn prove(
    circuit: &LayeredCircuit<BaseField>,
    witness: &CircuitWitness<BaseField>,
    transcript: &mut Transcript,
) -> GkrProof {
    prove_impl(circuit, witness, transcript, SparseLayerOracle::new)
}

/// Test-only: the same driver against the dense reference oracle. Used by
/// the observational-equivalence tests to compare whole proofs.
#[cfg(test)]
fn prove_dense(
    circuit: &LayeredCircuit<BaseField>,
    witness: &CircuitWitness<BaseField>,
    transcript: &mut Transcript,
) -> GkrProof {
    prove_impl(circuit, witness, transcript, DenseLayerOracle::new)
}

/// Verify a GKR proof against the circuit structure, the wiring oracle and
/// the claimed output values (all already absorbed into the transcript by
/// the caller). Returns the residual [`InputClaim`] the caller discharges.
///
/// FV-CONTRACT (Creusot, R2 - design contract, NOT tool-checked):
///   #[ensures(Ok(ic) ==> proof.layer_proofs.len() == circuit.layers.len()
///       && circuit.layers.len() > 0
///       && ic.point.len() == circuit.input_width_bits
///       && ic.point_y.len() == circuit.input_width_bits)]
/// This body is the Rust realisation of the model's chain-claim
/// threading: z_0 draw + m0 seed (`gkr_assembly_soundness`'s seeded
/// claim), per-layer `claim_i = sum_k c_k (target_k - const~(z_k))`,
/// the AFP round checks (via `ssgkr_sumcheck::verify`), the end-check
/// against the wiring reconstruction, and the `[(x*,1),(y*,r)]` carry
/// (`gkr_chain_bad`'s literal event shape, GKR_Assembly.thy). The
/// probability statement itself lives on the model side (SD-11 MODEL
/// BOUNDARY note).
/// TOOL WALL (R2 dev, narrowed by the verifier-acceptance strengthening):
/// only [`layer_reconstruction_matches`] opts out of translation for the
/// foreign extension-field equality. The shape, per-layer sequencing,
/// sumcheck-result branch, carry construction, and final-claim return below
/// remain ordinary non-trusted control flow.
pub fn verify<W: WiringOracle<ChallengeField>>(
    circuit: &LayeredCircuit<BaseField>,
    wiring: &W,
    claimed_outputs: &[BaseField],
    proof: &GkrProof,
    transcript: &mut Transcript,
) -> Result<InputClaim, GkrError> {
    let depth = circuit.layers.len();
    if depth == 0 {
        return Err(GkrError::ShapeMismatch);
    }
    if proof.layer_proofs.len() != depth {
        return Err(GkrError::ShapeMismatch);
    }

    let s_out0 = circuit.layers[0].width_bits;
    if s_out0 >= usize::BITS as usize {
        return Err(GkrError::ShapeMismatch);
    }
    if claimed_outputs.len() != 1usize << s_out0 {
        return Err(GkrError::ShapeMismatch);
    }
    let z0 = draw_point(transcript, s_out0);
    let m0 = mle_eval_base(claimed_outputs, &z0);
    let mut incoming = vec![(z0, ChallengeField::ONE)];
    let mut targets = vec![m0];

    for i in 0..depth {
        let s_in = if i + 1 < depth {
            circuit.layers[i + 1].width_bits
        } else {
            circuit.input_width_bits
        };
        let lp = &proof.layer_proofs[i];

        // claim_i = sum_k c_k (target_k - const~_i(z_k)).
        let claim: ChallengeField = incoming
            .iter()
            .zip(&targets)
            .map(|((z, c), t)| *c * (*t - wiring.eval_const_mle(i, z)))
            .sum();

        let instance = SumcheckInstance {
            num_vars: 2 * s_in,
            degree_bound: LAYER_ROUND_DEGREE,
            claimed_sum: claim,
        };
        let subclaim = ssgkr_sumcheck::verify(&instance, &lp.sumcheck, transcript)
            .map_err(|source| GkrError::Sumcheck { layer: i, source })?;

        let (xstar, ystar) = subclaim.point.split_at(s_in);
        transcript.observe_ext(lp.eval_x);
        transcript.observe_ext(lp.eval_y);

        // End-check: expected_eval == sum_k c_k P'_{z_k}(x*, y*).
        let beta_y = beta_eval(ystar);
        let ex = lp.eval_x;
        let ey = lp.eval_y;
        let mut rhs = ChallengeField::ZERO;
        for (z, c) in &incoming {
            let lin = wiring.eval_predicate_mle(i, GateKind::Lin, z, xstar, ystar);
            let mul = wiring.eval_predicate_mle(i, GateKind::Mul, z, xstar, ystar);
            let pow = wiring.eval_predicate_mle(i, GateKind::Pow3, z, xstar, ystar);
            let term = lin * ex * beta_y + mul * ex * ey + pow * ex * ex * ex * beta_y;
            rhs += *c * term;
        }
        if !layer_reconstruction_matches(rhs, subclaim.expected_eval) {
            return Err(GkrError::LayerClaimMismatch { layer: i });
        }

        if i + 1 < depth {
            let r = transcript.sample_challenge();
            incoming = vec![(xstar.to_vec(), ChallengeField::ONE), (ystar.to_vec(), r)];
            targets = vec![ex, ey];
        } else {
            return Ok(InputClaim {
                point: xstar.to_vec(),
                expected_eval: ex,
                point_y: ystar.to_vec(),
                expected_eval_y: ey,
            });
        }
    }

    Err(GkrError::ShapeMismatch)
}

/// The foreign extension-field equality used by the per-layer end-check.
///
/// Claim-free `trusted` means no relation between the returned Boolean and
/// Isabelle field equality is injected. The outer verifier merely records
/// and branches on the actual production computation.
#[cfg_attr(creusot, trusted)]
fn layer_reconstruction_matches(rhs: ChallengeField, expected: ChallengeField) -> bool {
    rhs == expected
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;
    use crate::circuit::{Gate, Layer, LayeredCircuit, evaluate_circuit};
    use crate::wiring::TableWiring;
    use ssgkr_primitives::field::PrimeCharacteristicRing;

    const TAG: &[u8] = b"gkr-core-test";

    fn f(x: u32) -> BaseField {
        BaseField::from_u32(x)
    }

    fn gate(kind: GateKind, out: u32, in1: u32, in2: u32, coeff: BaseField) -> Gate<BaseField> {
        Gate {
            kind,
            out,
            in1,
            in2,
            coeff,
        }
    }

    /// A two-layer circuit exercising every gate kind and a constant.
    /// inputs (width 4): [in0, in1, in2, in3]
    /// layer 1 (width 4): [in0+in1, in2*in3, in0^3, 5 + 2*in1]
    /// layer 0 (width 2): [w0*w1, w2+w3]
    fn mixed_circuit() -> LayeredCircuit<BaseField> {
        LayeredCircuit {
            layers: vec![
                Layer {
                    width_bits: 1,
                    gates: vec![
                        gate(GateKind::Mul, 0, 0, 1, f(1)),
                        gate(GateKind::Lin, 1, 2, 2, f(1)),
                        gate(GateKind::Lin, 1, 3, 3, f(1)),
                    ],
                    consts: vec![],
                },
                Layer {
                    width_bits: 2,
                    gates: vec![
                        gate(GateKind::Lin, 0, 0, 0, f(1)),
                        gate(GateKind::Lin, 0, 1, 1, f(1)),
                        gate(GateKind::Mul, 1, 2, 3, f(1)),
                        gate(GateKind::Pow3, 2, 0, 0, f(1)),
                        gate(GateKind::Lin, 3, 1, 1, f(2)),
                    ],
                    consts: vec![(3, f(5))],
                },
            ],
            input_width_bits: 2,
        }
    }

    /// A Mul-free circuit shaped like an affine + S-box hash round chain
    /// (the SMT workload shape): every layer is Lin/Pow3 + constants.
    fn affine_chain_circuit() -> LayeredCircuit<BaseField> {
        LayeredCircuit {
            layers: vec![
                // layer 0 (width 2): [t0^3, 3*t1 + 1]
                Layer {
                    width_bits: 1,
                    gates: vec![
                        gate(GateKind::Pow3, 0, 0, 0, f(1)),
                        gate(GateKind::Lin, 1, 1, 1, f(3)),
                    ],
                    consts: vec![(1, f(1))],
                },
                // layer 1 (width 2): [2*in0 + in1 + 7, in0^3]
                Layer {
                    width_bits: 1,
                    gates: vec![
                        gate(GateKind::Lin, 0, 0, 0, f(2)),
                        gate(GateKind::Lin, 0, 1, 1, f(1)),
                        gate(GateKind::Pow3, 1, 0, 0, f(1)),
                    ],
                    consts: vec![(0, f(7))],
                },
            ],
            input_width_bits: 1,
        }
    }

    /// Full acceptance: verify returns Ok AND the residual input claims match
    /// the real input MLE at both points (internal-verifier discharge).
    fn full_verify(
        circuit: &LayeredCircuit<BaseField>,
        claimed_outputs: &[BaseField],
        proof: &GkrProof,
        inputs: &[BaseField],
    ) -> bool {
        let wiring = TableWiring::new(circuit);
        let mut transcript = Transcript::new(TAG);
        transcript.observe_many(claimed_outputs);
        let claim = match verify(circuit, &wiring, claimed_outputs, proof, &mut transcript) {
            Ok(c) => c,
            Err(_) => return false,
        };
        mle_eval_base(inputs, &claim.point) == claim.expected_eval
            && mle_eval_base(inputs, &claim.point_y) == claim.expected_eval_y
    }

    fn prove_circuit(
        circuit: &LayeredCircuit<BaseField>,
        inputs: &[BaseField],
    ) -> (GkrProof, Vec<BaseField>) {
        let witness = evaluate_circuit(circuit, inputs).expect("evaluates");
        let outputs = witness.layer_values[0].clone();
        let mut transcript = Transcript::new(TAG);
        transcript.observe_many(&outputs);
        let proof = prove(circuit, &witness, &mut transcript);
        (proof, outputs)
    }

    #[test]
    fn mixed_circuit_roundtrip() {
        let circuit = mixed_circuit();
        let inputs = [f(2), f(3), f(4), f(5)];
        let (proof, outputs) = prove_circuit(&circuit, &inputs);
        assert!(full_verify(&circuit, &outputs, &proof, &inputs));
    }

    #[test]
    fn affine_chain_roundtrip() {
        let circuit = affine_chain_circuit();
        let inputs = [f(6), f(9)];
        let (proof, outputs) = prove_circuit(&circuit, &inputs);
        assert!(full_verify(&circuit, &outputs, &proof, &inputs));
    }

    #[test]
    fn rejects_empty_circuit_without_panicking() {
        let circuit = LayeredCircuit {
            layers: vec![],
            input_width_bits: 0,
        };
        let wiring = TableWiring::new(&circuit);
        let proof = GkrProof {
            layer_proofs: vec![],
        };
        let mut transcript = Transcript::new(TAG);

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            verify(&circuit, &wiring, &[], &proof, &mut transcript)
        }));

        assert!(matches!(result, Ok(Err(GkrError::ShapeMismatch))));
    }

    #[test]
    fn rejects_layer_proof_count_mismatch() {
        let circuit = mixed_circuit();
        let inputs = [f(2), f(3), f(4), f(5)];
        let (mut proof, outputs) = prove_circuit(&circuit, &inputs);
        proof.layer_proofs.pop();
        let wiring = TableWiring::new(&circuit);
        let mut transcript = Transcript::new(TAG);
        transcript.observe_many(&outputs);

        let result = verify(&circuit, &wiring, &outputs, &proof, &mut transcript);

        assert!(matches!(result, Err(GkrError::ShapeMismatch)));
    }

    #[test]
    fn rejects_machine_word_width_without_panicking() {
        let mut circuit = mixed_circuit();
        let inputs = [f(2), f(3), f(4), f(5)];
        let (proof, outputs) = prove_circuit(&circuit, &inputs);
        circuit.layers[0].width_bits = usize::BITS as usize;
        let wiring = TableWiring::new(&circuit);
        let mut transcript = Transcript::new(TAG);
        transcript.observe_many(&outputs);

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            verify(&circuit, &wiring, &outputs, &proof, &mut transcript)
        }));

        assert!(matches!(result, Ok(Err(GkrError::ShapeMismatch))));
    }

    #[test]
    fn rejects_tampered_output() {
        let circuit = mixed_circuit();
        let inputs = [f(2), f(3), f(4), f(5)];
        let (proof, mut outputs) = prove_circuit(&circuit, &inputs);
        outputs[0] += f(1); // claim a wrong output
        assert!(!full_verify(&circuit, &outputs, &proof, &inputs));
    }

    #[test]
    fn rejects_tampered_layer_eval() {
        let circuit = mixed_circuit();
        let inputs = [f(2), f(3), f(4), f(5)];
        let (mut proof, outputs) = prove_circuit(&circuit, &inputs);
        // Corrupt a claimed layer evaluation inside the proof.
        proof.layer_proofs[0].eval_x += ChallengeField::ONE;
        assert!(!full_verify(&circuit, &outputs, &proof, &inputs));
    }

    #[test]
    fn rejects_wrong_inputs_at_discharge() {
        // A proof for one input vector must not discharge against a different
        // input vector (this is what binds the witness in the internal model).
        let circuit = affine_chain_circuit();
        let inputs = [f(6), f(9)];
        let (proof, outputs) = prove_circuit(&circuit, &inputs);
        let other = [f(6), f(10)];
        assert!(full_verify(&circuit, &outputs, &proof, &inputs));
        assert!(!full_verify(&circuit, &outputs, &proof, &other));
    }

    #[test]
    fn rejects_tampered_round_poly() {
        let circuit = affine_chain_circuit();
        let inputs = [f(6), f(9)];
        let (mut proof, outputs) = prove_circuit(&circuit, &inputs);
        // Corrupt a sumcheck round polynomial coefficient.
        let rp = &proof.layer_proofs[0].sumcheck.round_polys[0];
        let mut coeffs = rp.coeffs().to_vec();
        coeffs[0] += ChallengeField::ONE;
        proof.layer_proofs[0].sumcheck.round_polys[0] = RoundPoly::from_coeffs(coeffs);
        assert!(!full_verify(&circuit, &outputs, &proof, &inputs));
    }

    // ---- 2d observational-equivalence tests (sparse oracle == dense) ----
    //
    // The whole point of the sparse oracle is that it produces a
    // bit-identical proof to the dense reference (same round polynomials =>
    // same transcript => same challenges => same everything). These tests
    // pin that down; if any of them ever needs the dense oracle relaxed or a
    // pre-existing test changed, that is a sign the equivalence broke.

    fn cf(x: u64) -> ChallengeField {
        cf_u64(x)
    }

    /// Prove `circuit` on `inputs` with both the dense reference and the
    /// production sparse oracle (identical transcript setup) and assert the
    /// whole proofs are bit-identical.
    fn assert_dense_sparse_equal(circuit: &LayeredCircuit<BaseField>, inputs: &[BaseField]) {
        let witness = evaluate_circuit(circuit, inputs).expect("evaluates");
        let outputs = witness.layer_values[0].clone();

        let mut td = Transcript::new(TAG);
        td.observe_many(&outputs);
        let dense = prove_dense(circuit, &witness, &mut td);

        let mut ts = Transcript::new(TAG);
        ts.observe_many(&outputs);
        let sparse = prove(circuit, &witness, &mut ts);

        assert_eq!(dense, sparse, "dense/sparse proof mismatch");
    }

    #[test]
    fn dense_sparse_agree_on_synthetic() {
        // The reduce.rs synthetic circuits: a mixed-gate circuit and a
        // Mul-free affine/S-box chain (the SMT workload shape).
        assert_dense_sparse_equal(&mixed_circuit(), &[f(2), f(3), f(4), f(5)]);
        assert_dense_sparse_equal(&affine_chain_circuit(), &[f(6), f(9)]);
    }

    /// Tiny deterministic PRNG (SplitMix64-style); no external rand crate.
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

    /// A random but structurally valid circuit: >= 3 layers (so the two-point
    /// alpha/beta carry path actually runs on interior layers), all gate
    /// kinds mixed, one output accumulating several gates, duplicate
    /// `(in1, in2)` Muls, optional consts, and non-uniform layer widths.
    fn random_circuit(rng: &mut Lcg) -> LayeredCircuit<BaseField> {
        let depth = 3 + rng.below(3) as usize; // 3..=5 layers
        let mut width_bits = Vec::with_capacity(depth);
        for _ in 0..depth {
            width_bits.push(1 + rng.below(3) as usize); // 1..=3
        }
        let input_width_bits = 1 + rng.below(3) as usize;

        let mut layers = Vec::with_capacity(depth);
        for i in 0..depth {
            let out_w = 1u32 << width_bits[i];
            let below_bits = if i + 1 < depth {
                width_bits[i + 1]
            } else {
                input_width_bits
            };
            let below_w = 1u32 << below_bits;

            let mut gates = Vec::new();
            let n_gates = 1 + rng.below(6); // 1..=6
            for _ in 0..n_gates {
                let (kind, coeff) = match rng.below(3) {
                    0 => (GateKind::Lin, f(rng.below(5))),
                    1 => (GateKind::Mul, f(rng.below(5))),
                    _ => (GateKind::Pow3, f(rng.below(5))),
                };
                let out = rng.below(out_w);
                let in1 = rng.below(below_w);
                // Unary kinds keep in2 == in1 (S-3 convention); Mul is free.
                let in2 = if matches!(kind, GateKind::Mul) {
                    rng.below(below_w)
                } else {
                    in1
                };
                gates.push(gate(kind, out, in1, in2, coeff));
            }
            // Sometimes book two Mul gates onto the SAME (out, in1, in2): one
            // output accumulating multiple gates AND a duplicate (in1, in2).
            if rng.below(2) == 0 {
                let out = rng.below(out_w);
                let in1 = rng.below(below_w);
                let in2 = rng.below(below_w);
                gates.push(gate(GateKind::Mul, out, in1, in2, f(1 + rng.below(3))));
                gates.push(gate(GateKind::Mul, out, in1, in2, f(1 + rng.below(3))));
            }
            let mut consts = Vec::new();
            if rng.below(2) == 0 {
                consts.push((rng.below(out_w), f(1 + rng.below(7))));
            }
            layers.push(Layer {
                width_bits: width_bits[i],
                gates,
                consts,
            });
        }
        LayeredCircuit {
            layers,
            input_width_bits,
        }
    }

    #[test]
    fn dense_sparse_agree_on_random() {
        for seed in 0..48u64 {
            let mut rng = Lcg::new(seed);
            let circuit = random_circuit(&mut rng);
            let in_len = 1usize << circuit.input_width_bits;
            let inputs: Vec<BaseField> = (0..in_len).map(|_| f(rng.below(17))).collect();
            assert_dense_sparse_equal(&circuit, &inputs);
        }
    }

    #[test]
    fn round_poly_trailing_zeros_preserved() {
        // One layer, s_in = 2 -> 2 x-rounds (degree 4) then 2 y-rounds
        // (degree <= 2). This fixes both round-level oracle equivalence and
        // the trailing-zero coefficients of the low-degree y-rounds (which,
        // if dropped, would change transcript absorption and split the
        // proof).
        let s_in = 2usize;
        let layer = Layer {
            width_bits: 2,
            gates: vec![
                gate(GateKind::Lin, 0, 1, 1, f(3)),
                gate(GateKind::Mul, 1, 2, 3, f(2)),
                gate(GateKind::Mul, 1, 2, 3, f(1)), // duplicate (in1, in2)
                gate(GateKind::Pow3, 2, 0, 0, f(1)),
                gate(GateKind::Lin, 3, 3, 3, f(4)),
            ],
            consts: vec![(0, f(5))],
        };
        // Two incoming points exercise the 2-point weight fold.
        let incoming = vec![(vec![cf(2), cf(5)], cf(1)), (vec![cf(7), cf(3)], cf(9))];
        let v_below = [f(4), f(6), f(9), f(2)]; // 2^s_in = 4 values
        let challenges = [cf(3), cf(7), cf(11), cf(13)];

        let mut dense = DenseLayerOracle::new(&layer, s_in, &incoming, &v_below);
        let mut sparse = SparseLayerOracle::new(&layer, s_in, &incoming, &v_below);
        assert_eq!(dense.num_vars(), 2 * s_in);
        assert_eq!(sparse.num_vars(), 2 * s_in);

        // challenges.len() == 2 * s_in, one per round.
        for (round, &r) in challenges.iter().enumerate() {
            let gd = dense.round_poly();
            let gs = sparse.round_poly();
            // Full coefficient-vector identity (length and trailing zeros).
            assert_eq!(gd, gs, "round {round}");
            assert_eq!(gs.coeffs().len(), 5, "round {round} coeff length");
            if round >= s_in {
                // y-rounds are degree <= 2 in BOTH oracles: the top two
                // coefficients are trailing zeros.
                let zero = ChallengeField::ZERO;
                assert_eq!(gs.coeffs()[3], zero, "round {round} sparse c3");
                assert_eq!(gs.coeffs()[4], zero, "round {round} sparse c4");
                assert_eq!(gd.coeffs()[3], zero, "round {round} dense c3");
                assert_eq!(gd.coeffs()[4], zero, "round {round} dense c4");
            }
            dense.bind(r);
            sparse.bind(r);
        }
    }
}
