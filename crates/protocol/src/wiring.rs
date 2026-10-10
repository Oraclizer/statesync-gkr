//! Wiring predicate MLE oracles.
//!
//! The GKR layer identity ties layer i values to layer i+1 values
//! (S-3 amended algebra - gate coefficients live inside the F-valued
//! predicates, additive constants in one extra multilinear term):
//!
//! ```text
//! V_i(z) = const~(z)
//!        + sum over x     of  lin~(z,x)   * V_{i+1}(x)
//!        + sum over (x,y) of  mul~(z,x,y) * V_{i+1}(x) * V_{i+1}(y)
//!        + sum over x     of  pow3~(z,x)  * V_{i+1}(x)^3
//! ```
//!
//! where `~` denotes the multilinear extension of the per-gate-kind
//! WEIGHTED wiring predicates (F-valued sparse functions: the gate
//! coefficient is the predicate value at that index tuple; unary kinds
//! live on `(z, x)` pairs). The verifier must evaluate these MLEs at
//! random points WITHOUT materializing full tables; how cheaply that
//! works depends entirely on wiring regularity.
//!
//! Strategy A (default): one SMT tree level = one logical GKR layer with
//! DATA-PARALLEL regular wiring - the predicate is identical across
//! levels, so its (closed-form) evaluation is derived once and reused,
//! which is also what keeps the FV cost at "one predicate lemma, reused
//! by induction over tree height".

use std::collections::BTreeMap;

use ssgkr_primitives::field::{BaseField, ChallengeField, Field, PrimeCharacteristicRing};

#[cfg(creusot)]
use creusot_std::prelude::{Int, logic, pearlite, requires, trusted};

use crate::circuit::{Gate, GateKind, Layer, LayeredCircuit};
use crate::mle::{embed, eq_point_index, eq_points, eq3_points};

/// Verifier-side (and prover-side) access to wiring predicate MLEs.
///
/// SEAL[S-3-adjacent]: this trait is the seam between circuit structure
/// and the sumcheck chain; implementations may be table-based (small
/// tests) or closed-form (regular SMT wiring, the production path).
pub trait WiringOracle<F: Field> {
    /// Logical view of the number of layers this oracle answers for -
    /// the valid `layer` index domain of every method below
    /// (verification builds only). S-3-adjacent seal EXTENSION,
    /// supervisor/Jay-approved at the 3b refinement close-out
    /// (refinement_status 16.7 decision 2, executed in section 17): a
    /// `cfg(creusot)` contract-only member, so the production trait
    /// surface is unchanged. The bound mirrors the model's structural
    /// index domain - the chain facts quantify layers by position
    /// (`i < length Ls`, GKR_Assembly.thy) and the per-layer MLE
    /// functions take the layer itself (Wiring_MLE.thy), so "the oracle
    /// is only asked about layers that exist" is the interface-level
    /// domain condition.
    #[cfg(creusot)]
    #[logic]
    fn n_layers(self) -> Int;

    /// log2 width of layer `i` (the "z" variables).
    #[cfg_attr(creusot, requires(layer@ < self.n_layers()))]
    fn out_width_bits(&self, layer: usize) -> usize;

    /// log2 width of layer `i+1` (the "x"/"y" variables).
    #[cfg_attr(creusot, requires(layer@ < self.n_layers()))]
    fn in_width_bits(&self, layer: usize) -> usize;

    /// Evaluate the WEIGHTED predicate MLE for `kind` at `(z, x, y)`.
    /// For unary kinds (`Lin`, `Pow3`) the `y` block is ignored (the
    /// predicate lives on `(z, x)`); callers pass `y = x` by convention.
    ///
    /// FV-CONTRACT (Creusot, R2): on boolean points the MLE agrees with
    /// the layer's weighted wiring (the gate coefficient at that tuple,
    /// zero elsewhere) - the per-strategy core lemma of Theorem B.
    /// The layer-index domain requires is ACTIVE (S-3 seal extension).
    #[cfg_attr(creusot, requires(layer@ < self.n_layers()))]
    fn eval_predicate_mle(&self, layer: usize, kind: GateKind, z: &[F], x: &[F], y: &[F]) -> F;

    /// Evaluate the MLE of the layer's additive constant vector at `z`
    /// (the `const~(z)` term of the layer identity).
    #[cfg_attr(creusot, requires(layer@ < self.n_layers()))]
    fn eval_const_mle(&self, layer: usize, z: &[F]) -> F;
}

/// One gate of a per-block template (local wire indices within a block).
///
/// `PartialEq`/`Eq` gated out of the Creusot build (`coeff` is a foreign
/// field element; see `ssgkr_sumcheck::MultilinearPoly`).
#[derive(Clone, Copy, Debug)]
#[cfg_attr(not(creusot), derive(PartialEq, Eq))]
pub struct LocalGate {
    /// Gate kind.
    pub kind: GateKind,
    /// Local output wire.
    pub out: u32,
    /// Local first input wire.
    pub in1: u32,
    /// Local second input wire (== `in1` for unary kinds).
    pub in2: u32,
    /// Multiplicative coefficient.
    pub coeff: BaseField,
}

/// One layer of a data-parallel regular circuit: `2^copy_bits` identical
/// blocks side by side, each block laid out from the same gate/const
/// template over local wire indices. The block index is the HIGH part of a
/// global wire index (`global = block * 2^local_bits + local`).
#[derive(Clone, Debug)]
pub struct RegularLayer {
    /// log2(number of identical blocks).
    pub copy_bits: usize,
    /// log2(block output width).
    pub out_local_bits: usize,
    /// log2(block input width).
    pub in_local_bits: usize,
    /// Per-block gate template (local indices).
    pub gates: Vec<LocalGate>,
    /// Per-block additive constants (local output wire, value).
    pub consts: Vec<(u32, BaseField)>,
}

/// Closed-form oracle for data-parallel regular wiring (strategy A).
///
/// The load-bearing identity: because every block is identical and the
/// block index is the high bit-block of a wire, each per-kind wiring
/// predicate FACTORS as
///
/// ```text
/// pred~(z, x)     = eq(z_hi, x_hi) * template~(z_lo, x_lo)          (unary)
/// mul~(z, x, y)   = eq(z_hi, x_hi) * eq(z_hi, y_hi) * mul_template~(z_lo, x_lo, y_lo)
/// const~(z)       = const_template~(z_lo)     (blocks are const-uniform; sum_b eq = 1)
/// ```
///
/// where `_hi` is the `copy_bits` block prefix and `_lo` the local suffix.
/// The template sum is `O(template gates)`, `eq` is `O(copy_bits)` - so
/// evaluation is `O(polylog + block size)`, the succinct verifier cost,
/// independent of the tree height. This is the "one predicate lemma reused
/// by induction over levels" of Theorem B; [`Self::materialize`] expands the
/// templates and the tests cross-check this closed form against
/// [`TableWiring`] on the materialized circuit.
#[derive(Clone, Debug)]
pub struct RegularWiring {
    /// Per-layer templates, output layer first (same order as `LayeredCircuit`).
    pub layers: Vec<RegularLayer>,
}

impl RegularWiring {
    /// Expand the templates into a concrete data-parallel circuit.
    pub fn materialize(&self) -> LayeredCircuit<BaseField> {
        let mut layers = Vec::with_capacity(self.layers.len());
        for lay in &self.layers {
            let blocks = 1u32 << lay.copy_bits;
            let out_block = 1u32 << lay.out_local_bits;
            let in_block = 1u32 << lay.in_local_bits;
            let mut gates = Vec::with_capacity(blocks as usize * lay.gates.len());
            let mut consts = Vec::with_capacity(blocks as usize * lay.consts.len());
            for b in 0..blocks {
                for g in &lay.gates {
                    gates.push(Gate {
                        kind: g.kind,
                        out: b * out_block + g.out,
                        in1: b * in_block + g.in1,
                        in2: b * in_block + g.in2,
                        coeff: g.coeff,
                    });
                }
                for &(lc, cv) in &lay.consts {
                    consts.push((b * out_block + lc, cv));
                }
            }
            layers.push(Layer {
                width_bits: lay.copy_bits + lay.out_local_bits,
                gates,
                consts,
            });
        }
        let input_width_bits = self
            .layers
            .last()
            .map(|l| l.copy_bits + l.in_local_bits)
            .unwrap_or(0);
        LayeredCircuit {
            layers,
            input_width_bits,
        }
    }
}

impl WiringOracle<ChallengeField> for RegularWiring {
    /// Logical view of the template-layer count (S-3 seal extension -
    /// see the trait). Contracts are restated on the impl methods: this
    /// toolchain rev does not inherit trait contracts into impls (the
    /// R1 `HashGadget` restatement convention).
    #[cfg(creusot)]
    #[logic]
    fn n_layers(self) -> Int {
        pearlite! { self.layers@.len() }
    }

    #[cfg_attr(creusot, requires(layer@ < self.n_layers()))]
    fn out_width_bits(&self, layer: usize) -> usize {
        let l = &self.layers[layer];
        l.copy_bits + l.out_local_bits
    }

    #[cfg_attr(creusot, requires(layer@ < self.n_layers()))]
    fn in_width_bits(&self, layer: usize) -> usize {
        let l = &self.layers[layer];
        l.copy_bits + l.in_local_bits
    }

    #[cfg_attr(creusot, requires(layer@ < self.n_layers()))]
    fn eval_predicate_mle(
        &self,
        layer: usize,
        kind: GateKind,
        z: &[ChallengeField],
        x: &[ChallengeField],
        y: &[ChallengeField],
    ) -> ChallengeField {
        let lay = &self.layers[layer];
        let cb = lay.copy_bits;
        let (z_hi, z_lo) = z.split_at(cb);
        let (x_hi, x_lo) = x.split_at(cb);
        let is_mul = matches!(kind, GateKind::Mul);

        // Block-match factor: unary gates need out and in in the SAME block
        // (two-way eq); a binary gate needs out, in1 AND in2 all in one block
        // (three-way eq, not a product of two-way eqs).
        let (block, y_lo): (ChallengeField, &[ChallengeField]) = if is_mul {
            let (y_hi, y_lo) = y.split_at(cb);
            (eq3_points(z_hi, x_hi, y_hi), y_lo)
        } else {
            (eq_points(z_hi, x_hi), &[])
        };

        let mut tmpl = ChallengeField::ZERO;
        for g in &lay.gates {
            if g.kind != kind {
                continue;
            }
            let mut t = embed(g.coeff)
                * eq_point_index(z_lo, g.out as usize)
                * eq_point_index(x_lo, g.in1 as usize);
            if is_mul {
                t *= eq_point_index(y_lo, g.in2 as usize);
            }
            tmpl += t;
        }
        block * tmpl
    }

    #[cfg_attr(creusot, requires(layer@ < self.n_layers()))]
    fn eval_const_mle(&self, layer: usize, z: &[ChallengeField]) -> ChallengeField {
        let lay = &self.layers[layer];
        let z_lo = &z[lay.copy_bits..];
        // sum_b eq(z_hi, b) = 1, so only the (block-uniform) local template
        // survives.
        let mut acc = ChallengeField::ZERO;
        for &(wire, val) in &lay.consts {
            acc += embed(val) * eq_point_index(z_lo, wire as usize);
        }
        acc
    }
}

/// Materialized wiring oracle: evaluates every predicate MLE by summing the
/// sparse per-gate contributions of a concrete circuit.
///
/// This is the GENERAL, always-correct oracle (predicate eval costs
/// `O(#gates)`, not the succinct closed forms of [`RegularWiring`] /
/// [`DerivedRegularWiring`]). It is the REFERENCE the closed-form oracles
/// are cross-checked against - the FV-CONTRACT "MLE agrees with the
/// weighted wiring" made executable - and the audit anchor the 2b/2d
/// adversarial suites validated. The production verifier now runs the
/// derived closed form; this stays callable (facade
/// `verify_sync_op_reference`) so the two can always be compared
/// verdict-for-verdict.
pub struct TableWiring<'a> {
    circuit: &'a LayeredCircuit<BaseField>,
}

impl<'a> TableWiring<'a> {
    /// Wrap a circuit as a materialized wiring oracle.
    pub fn new(circuit: &'a LayeredCircuit<BaseField>) -> Self {
        Self { circuit }
    }
}

impl WiringOracle<ChallengeField> for TableWiring<'_> {
    /// Logical view of the wrapped circuit's layer count (S-3 seal
    /// extension - see the trait). Contracts are restated on the impl
    /// methods (no trait-contract inheritance at this rev). With the
    /// index-domain requires in force the two width bodies are fully
    /// machine-checked (their single residual goal was exactly this
    /// bound). The two eval bodies keep one residual goal each: their vc
    /// is a merged chunk that split_vc cannot decompose - the
    /// layer-index face is discharged by the requires (the width greens
    /// are the direct evidence of that face closing), and the remainder
    /// diverges the solvers at this rev (R1 wall-2 phenomenology; a
    /// Form-C retry with AddAssign/MulAssign claim-free specs and
    /// bridge-axiom loop invariants was measured no-score and reverted;
    /// corrected diagnosis vs refinement_status 14.5, see section 17).
    #[cfg(creusot)]
    #[logic]
    fn n_layers(self) -> Int {
        pearlite! { self.circuit.layers@.len() }
    }

    #[cfg_attr(creusot, requires(layer@ < self.n_layers()))]
    fn out_width_bits(&self, layer: usize) -> usize {
        self.circuit.layers[layer].width_bits
    }

    #[cfg_attr(creusot, requires(layer@ < self.n_layers()))]
    fn in_width_bits(&self, layer: usize) -> usize {
        if layer + 1 < self.circuit.layers.len() {
            self.circuit.layers[layer + 1].width_bits
        } else {
            self.circuit.input_width_bits
        }
    }

    #[cfg_attr(creusot, requires(layer@ < self.n_layers()))]
    fn eval_predicate_mle(
        &self,
        layer: usize,
        kind: GateKind,
        z: &[ChallengeField],
        x: &[ChallengeField],
        y: &[ChallengeField],
    ) -> ChallengeField {
        let layer = &self.circuit.layers[layer];
        let mut acc = ChallengeField::ZERO;
        for g in &layer.gates {
            if g.kind != kind {
                continue;
            }
            let mut term = embed(g.coeff)
                * eq_point_index(z, g.out as usize)
                * eq_point_index(x, g.in1 as usize);
            // Binary kinds also constrain the `y` block; unary kinds live on
            // (z, x) only (in2 == in1 by the S-3 convention).
            if matches!(kind, GateKind::Mul) {
                term *= eq_point_index(y, g.in2 as usize);
            }
            acc += term;
        }
        acc
    }

    #[cfg_attr(creusot, requires(layer@ < self.n_layers()))]
    fn eval_const_mle(&self, layer: usize, z: &[ChallengeField]) -> ChallengeField {
        let layer = &self.circuit.layers[layer];
        let mut acc = ChallengeField::ZERO;
        for &(wire, val) in &layer.consts {
            acc += embed(val) * eq_point_index(z, wire as usize);
        }
        acc
    }
}

// ---------------------------------------------------------------------------
// Derived closed-form wiring (the succinct verifier path for COMPILED
// circuits): the RegularWiring factorization generalized from "one uniform
// block family per layer" to "any set of gate families in aligned arithmetic
// progression", so it can be DERIVED from a builder-laid-out circuit instead
// of requiring the circuit to be hand-shaped around one template.
// ---------------------------------------------------------------------------

/// A layout hint: which data-parallel FAMILY a gate/const belongs to and
/// which BLOCK (instance) within it. Emitted by the circuit builder next to
/// the circuit. Semantically OPAQUE here (this crate stays workload-generic,
/// S-1) and soundness-irrelevant: hints only propose groupings, and
/// [`DerivedRegularWiring::derive`] re-verifies every proposed progression
/// gate-by-gate, dropping anything that does not fit to the exact sparse
/// path. Wrong hints can only cost performance, never correctness.
///
/// All-`u32` payload: the Creusot build derives a `DeepModel` (class-2
/// container, R1 boundary rule) so `PartialEq` stays available.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(creusot, derive(creusot_std::prelude::DeepModel))]
pub struct FamilyTag {
    /// Family identifier (builder-chosen, opaque).
    pub family: u32,
    /// Block (instance) index within the family.
    pub block: u32,
}

/// Per-layer tags, parallel to `Layer::gates` and `Layer::consts`.
#[derive(Clone, Debug, Default)]
pub struct LayerHints {
    /// One tag per gate (same order as `Layer::gates`).
    pub gates: Vec<Option<FamilyTag>>,
    /// One tag per constant (same order as `Layer::consts`).
    pub consts: Vec<Option<FamilyTag>>,
}

/// Layout hints for a whole circuit (same layer order as the circuit).
#[derive(Clone, Debug, Default)]
pub struct WiringHints {
    /// Per-layer hints, output layer first.
    pub layers: Vec<LayerHints>,
}

/// `sum_{b=0}^{count-1} prod_t eq(points[t], bases[t] + b)` in `O(log^2)`
/// field work (dyadic range split + carry DP over the free bits) instead of
/// `O(count)` - the block-matching factor of the derived closed form.
///
/// This generalizes the uniform-block identities: with all bases zero and
/// `count = 2^m` it equals `eq_points` (two terms) / `eq3_points` (three
/// terms). Arbitrary bases are what let the factorization survive a packed
/// builder layout, where families start at aligned but nonzero offsets.
///
/// Requires `bases[t] + count <= 2^{points[t].len()}` for every term (all
/// enumerated indices representable in that side's variables). An empty
/// `terms` means an empty product, so the sum is `count` embedded in the
/// field.
///
/// FV-CONTRACT (Creusot, R2 - design contract, NOT tool-checked): the
/// full-range two-term instance equals the per-variable product closed
/// form (`Wiring_MLE.srange_full_two_terms`); the partial-range carry-DP
/// closed form is an evaluation algorithm outside the model's scope
/// (held by the executable pins in tests/verify_succinct.rs).
/// TOOL WALL (R2 dev, honest carry-over; `#[trusted]` = translation
/// opt-out carrying ZERO claims): the body compares field elements
/// (`w == ChallengeField::ZERO` skip guards) and the foreign type cannot
/// carry `DeepModel` (orphan rule; the E0277 wall of
/// `ssgkr_sumcheck::verify`); its index bookkeeping is u64 bit
/// arithmetic, axiom-free in the int-mode prelude (R1 wall 3,
/// upstream not_planned).
#[cfg_attr(creusot, trusted)]
pub fn shifted_range_eq(terms: &[(&[ChallengeField], u64)], count: u64) -> ChallengeField {
    // phi(point, j, bit): the eq factor of value-bit j (LSB = 0) of an
    // index. Variable 0 is the MSB, so bit j lives at point[len - 1 - j].
    #[inline]
    fn phi(point: &[ChallengeField], j: u32, bit: u64) -> ChallengeField {
        let p = point[point.len() - 1 - j as usize];
        if bit == 1 { p } else { ChallengeField::ONE - p }
    }

    if terms.is_empty() {
        return ChallengeField::from(BaseField::from_u64(count));
    }
    let nstates = 1usize << terms.len();
    let mut total = ChallengeField::ZERO;

    // Dyadic decomposition: [0, count) as disjoint blocks [h, h + 2^i), one
    // per set bit of `count`, high bits first.
    let mut h = 0u64;
    for i in (0..64u32).rev() {
        if count & (1u64 << i) == 0 {
            continue;
        }
        // Within the block, b = h + f with f < 2^i free; per term the index
        // is a[t] + f with a[t] = bases[t] + h. Walk the i free bit
        // positions LSB-first, tracking one addition carry per term (the DP
        // state), multiplying in the eq factor of each produced sum bit.
        let a: Vec<u64> = terms.iter().map(|&(_, base)| base + h).collect();
        let mut states = vec![ChallengeField::ZERO; nstates];
        states[0] = ChallengeField::ONE;
        for j in 0..i {
            let mut next = vec![ChallengeField::ZERO; nstates];
            for (st, &w) in states.iter().enumerate() {
                if w == ChallengeField::ZERO {
                    continue;
                }
                for fbit in 0..2u64 {
                    let mut w2 = w;
                    let mut st2 = 0usize;
                    for (t, &(point, _)) in terms.iter().enumerate() {
                        let ab = (a[t] >> j) & 1;
                        let carry = ((st >> t) & 1) as u64;
                        let s = ab ^ fbit ^ carry;
                        if ((ab & fbit) | (fbit & carry) | (ab & carry)) == 1 {
                            st2 |= 1 << t;
                        }
                        w2 *= phi(point, j, s);
                    }
                    next[st2] += w2;
                }
            }
            states = next;
        }
        // Bits >= i of the index are the fixed value (a[t] >> i) + carry.
        for (st, &w) in states.iter().enumerate() {
            if w == ChallengeField::ZERO {
                continue;
            }
            let mut w2 = w;
            for (t, &(point, _)) in terms.iter().enumerate() {
                let carry = ((st >> t) & 1) as u64;
                let rest = (a[t] >> i) + carry;
                let n = point.len() as u32;
                debug_assert!(i <= n && (rest >> (n - i)) == 0, "index out of range");
                for j in i..n {
                    w2 *= phi(point, j, (rest >> (j - i)) & 1);
                }
            }
            total += w2;
        }
        h += 1u64 << i;
    }
    total
}

/// `eq(point, idx)` for every `idx < 2^{point.len()}` (MSB-first indexing,
/// same convention as [`eq_point_index`]), built in `O(2^n)` by doubling.
/// Used for the LOCAL (within-block) tap offsets, whose width is a few bits,
/// so each tap costs O(1) multiplications instead of O(width).
fn eq_table(point: &[ChallengeField]) -> Vec<ChallengeField> {
    let mut t = vec![ChallengeField::ONE];
    for &p in point {
        let q = ChallengeField::ONE - p;
        let mut next = Vec::with_capacity(t.len() * 2);
        for &e in &t {
            next.push(e * q);
            next.push(e * p);
        }
        t = next;
    }
    t
}

/// One side (out / in1 / in2) of a derived gate group. Block `b`'s wire for
/// a tap with offset `off` is `((base_hi + b) << lb) + off` (a stride-`2^lb`
/// progression from an aligned base), or one fixed wire shared by every
/// block.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Side {
    /// Aligned arithmetic progression: high part walks `base_hi + b`.
    Prog {
        /// Index high part of block 0 (`base >> lb`).
        base_hi: u64,
        /// log2 of the stride; also the local offset width.
        lb: u32,
    },
    /// The same wire for every block (degenerate progression, stride 0).
    Fixed {
        /// The shared wire index.
        wire: u64,
    },
}

/// Manual `Int` deep model (R1 boundary rule: derived `Ord` demands a
/// `DeepModelTy` with `OrdLogic`, which the derived wrapper model lacks
/// - AssetId precedent). `Side` is a `BTreeMap` key, so `Ord` must stay
/// live under Creusot. The encoding is order-preserving and injective:
/// `Prog` variants occupy `[0, 2^96)` lexicographically by
/// `(base_hi, lb)` (`lb < 2^32`), `Fixed` variants live above `2^96` -
/// matching the derived discriminant-then-fields order.
#[cfg(creusot)]
impl creusot_std::model::DeepModel for Side {
    type DeepModelTy = Int;

    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! {
            match self {
                Side::Prog { base_hi, lb } => base_hi@ * 4294967296 + lb@,
                Side::Fixed { wire } => 79228162514264337593543950336 + wire@,
            }
        }
    }
}

impl Side {
    /// Local offset width in bits (0 for a fixed side).
    fn lb(&self) -> u32 {
        match *self {
            Side::Prog { lb, .. } => lb,
            Side::Fixed { .. } => 0,
        }
    }

    /// Concrete wire index of block `b` at local offset `off`.
    fn wire(&self, b: u64, off: u32) -> u64 {
        match *self {
            Side::Prog { base_hi, lb } => ((base_hi + b) << lb) + off as u64,
            Side::Fixed { wire } => wire,
        }
    }
}

/// One derived family group: `count` blocks whose taps follow the group's
/// side progressions. The predicate MLE restricted to this group factors as
/// `D * T`: `D` = the block-matching factor over the sides' high parts
/// ([`shifted_range_eq`]), `T` = the local template sum over tap offsets.
#[derive(Clone, Debug)]
struct GateGroup {
    count: u64,
    out: Side,
    in1: Side,
    in2: Side,
    /// `(out_off, in1_off, coeff)` per unary tap.
    lin: Vec<(u32, u32, BaseField)>,
    /// `(out_off, in1_off, coeff)` per unary tap.
    pow3: Vec<(u32, u32, BaseField)>,
    /// `(out_off, in1_off, in2_off, coeff)` per binary tap.
    mul: Vec<(u32, u32, u32, BaseField)>,
}

/// A derived constant family: block-uniform values on an out progression.
#[derive(Clone, Debug)]
struct ConstGroup {
    count: u64,
    out: Side,
    /// `(out_off, value)` per block-template constant.
    vals: Vec<(u32, BaseField)>,
}

/// One derived layer: closed-form groups plus the exact sparse remainder.
#[derive(Clone, Debug)]
struct DerivedLayer {
    groups: Vec<GateGroup>,
    sparse_gates: Vec<Gate<BaseField>>,
    const_groups: Vec<ConstGroup>,
    sparse_consts: Vec<(u32, BaseField)>,
    out_bits: usize,
    in_bits: usize,
}

/// Coverage statistics of a derivation (how much of the circuit the closed
/// form captured). Sparse leftovers are CORRECT but cost `O(1)` per gate per
/// evaluation, so tests pin the sparse fraction to keep the verifier
/// succinct in fact, not just in intent.
///
/// `PartialEq`/`Eq` gated out of the Creusot build (no contract consumes
/// stats equality).
#[derive(Clone, Copy, Debug, Default)]
#[cfg_attr(not(creusot), derive(PartialEq, Eq))]
pub struct DerivedStats {
    /// Closed-form groups across all layers.
    pub groups: usize,
    /// Gates covered by closed-form groups (block-expanded count).
    pub grouped_gates: usize,
    /// Gates left on the exact sparse path.
    pub sparse_gates: usize,
    /// Constants covered by closed-form groups (block-expanded count).
    pub grouped_consts: usize,
    /// Constants left on the exact sparse path.
    pub sparse_consts: usize,
}

/// Closed-form wiring oracle DERIVED from a compiled circuit plus layout
/// hints - the production succinct-verifier path (design D-33 (6) realized:
/// "derive the RegularWiring closed form from the compiled SMT circuit").
///
/// # Correctness model (N2)
///
/// The derivation is an exact REPARTITION of each layer's gate/const lists:
/// every gate lands either in a verified progression group or on the sparse
/// path, never dropped or duplicated (the tag grouping partitions gate
/// indices; each group's per-slot progression is checked against every
/// member gate before it is accepted). Evaluation then only re-associates
/// the same field sum - `eq(z, ((A + b) << lb) + off)` factors EXACTLY into
/// `eq(z_hi, A + b) * eq(z_lo, off)` when offsets stay below the stride -
/// so the oracle is bit-identical to [`TableWiring`] on the same circuit,
/// which the cross-oracle tests pin on the real compiled circuits.
///
/// # Cost
///
/// Per predicate evaluation: `O(groups * (log^2 + template))` instead of
/// `O(#gates)`; for the SMT circuits the per-layer template count is set by
/// the hash width, not the tree depth, which is what restores the succinct
/// GKR verifier.
#[derive(Clone, Debug)]
pub struct DerivedRegularWiring {
    layers: Vec<DerivedLayer>,
}

/// Widest local-offset table the derivation will build per side. A group
/// whose offsets need more bits than this is dumped to the sparse path
/// (the table would cost more than it saves).
const MAX_LOCAL_BITS: u32 = 12;

impl DerivedRegularWiring {
    /// Derive the closed form for `circuit` using `hints`. Infallible:
    /// anything that does not fit a verified aligned progression falls back
    /// to the exact sparse path (correct, just not succinct), so hints can
    /// never make the oracle wrong.
    pub fn derive(circuit: &LayeredCircuit<BaseField>, hints: &WiringHints) -> Self {
        let depth = circuit.layers.len();
        let empty = LayerHints::default();
        let mut layers = Vec::with_capacity(depth);
        for (li, layer) in circuit.layers.iter().enumerate() {
            let in_bits = if li + 1 < depth {
                circuit.layers[li + 1].width_bits
            } else {
                circuit.input_width_bits
            };
            let lh = hints.layers.get(li).unwrap_or(&empty);
            layers.push(derive_layer(layer, lh, layer.width_bits, in_bits));
        }
        Self { layers }
    }

    /// Re-expand `layer`'s derived groups plus sparse remainder back into a
    /// concrete gate list. Audit helper for the "exact repartition" property
    /// (N2): the result must be a PERMUTATION of the source circuit layer's
    /// gate list - nothing dropped, added, or altered - which the derived-
    /// vs-table equivalence tests check on the real compiled circuits.
    pub fn expand_gates(&self, layer: usize) -> Vec<Gate<BaseField>> {
        let lay = &self.layers[layer];
        let mut out = Vec::new();
        for grp in &lay.groups {
            for b in 0..grp.count {
                for &(o, i1, coeff) in &grp.lin {
                    let in1 = grp.in1.wire(b, i1) as u32;
                    out.push(Gate {
                        kind: GateKind::Lin,
                        out: grp.out.wire(b, o) as u32,
                        in1,
                        in2: in1,
                        coeff,
                    });
                }
                for &(o, i1, coeff) in &grp.pow3 {
                    let in1 = grp.in1.wire(b, i1) as u32;
                    out.push(Gate {
                        kind: GateKind::Pow3,
                        out: grp.out.wire(b, o) as u32,
                        in1,
                        in2: in1,
                        coeff,
                    });
                }
                for &(o, i1, i2, coeff) in &grp.mul {
                    out.push(Gate {
                        kind: GateKind::Mul,
                        out: grp.out.wire(b, o) as u32,
                        in1: grp.in1.wire(b, i1) as u32,
                        in2: grp.in2.wire(b, i2) as u32,
                        coeff,
                    });
                }
            }
        }
        out.extend(lay.sparse_gates.iter().copied());
        out
    }

    /// Re-expand `layer`'s constants (companion of [`Self::expand_gates`]).
    pub fn expand_consts(&self, layer: usize) -> Vec<(u32, BaseField)> {
        let lay = &self.layers[layer];
        let mut out = Vec::new();
        for grp in &lay.const_groups {
            for b in 0..grp.count {
                for &(o, v) in &grp.vals {
                    out.push((grp.out.wire(b, o) as u32, v));
                }
            }
        }
        out.extend(lay.sparse_consts.iter().copied());
        out
    }

    /// Coverage statistics across all layers (see [`DerivedStats`]).
    pub fn stats(&self) -> DerivedStats {
        let mut s = DerivedStats::default();
        for lay in &self.layers {
            s.groups += lay.groups.len();
            for g in &lay.groups {
                s.grouped_gates += (g.lin.len() + g.pow3.len() + g.mul.len()) * g.count as usize;
            }
            for c in &lay.const_groups {
                s.grouped_consts += c.vals.len() * c.count as usize;
            }
            s.sparse_gates += lay.sparse_gates.len();
            s.sparse_consts += lay.sparse_consts.len();
        }
        s
    }
}

/// Fit one side of a slot across `c >= 2` blocks: the values must form an
/// arithmetic progression with a power-of-two stride whose base is aligned
/// to the stride at the offset's granularity (which holds automatically:
/// `(v0 + b * 2^lb) >> lb == (v0 >> lb) + b` for any `v0`).
/// TOOL WALL (R2 dev; `#[trusted]` = translation opt-out, ZERO claims):
/// u64 bit arithmetic (shift/mask fitting) is axiom-free in the int-mode
/// prelude (R1 wall 3). Hint-fitting is soundness-inert by construction
/// (`derive` re-verifies every progression gate by gate; a wrong fit only
/// costs the sparse fallback).
#[cfg_attr(creusot, trusted)]
fn fit_progression(vals: &[u64]) -> Option<(Side, u32)> {
    let v0 = vals[0];
    let d = vals[1].checked_sub(v0)?;
    for (b, &v) in vals.iter().enumerate() {
        if v != v0 + b as u64 * d {
            return None;
        }
    }
    if d == 0 {
        return Some((Side::Fixed { wire: v0 }, 0));
    }
    if !d.is_power_of_two() {
        return None;
    }
    let lb = d.trailing_zeros();
    if lb > MAX_LOCAL_BITS {
        return None;
    }
    let off = (v0 & (d - 1)) as u32;
    Some((
        Side::Prog {
            base_hi: v0 >> lb,
            lb,
        },
        off,
    ))
}

/// Fit one side of a SINGLE-block family over all its values jointly: find
/// the smallest aligned window containing them (`(min >> lb) == (max >> lb)`)
/// and use window-relative offsets. With `count == 1` the block factor
/// degenerates to a point eq at the window prefix.
/// TOOL WALL (R2 dev; `#[trusted]` = translation opt-out, ZERO claims):
/// same walls as [`fit_progression`] (bit arithmetic + iterator
/// min/max specs); soundness-inert hint fitting.
#[cfg_attr(creusot, trusted)]
fn fit_window(vals: &[u64]) -> Option<(Side, Vec<u32>)> {
    let &min = vals.iter().min()?;
    let &max = vals.iter().max()?;
    let mut lb = 0u32;
    while (min >> lb) != (max >> lb) {
        lb += 1;
        if lb > MAX_LOCAL_BITS {
            return None;
        }
    }
    let base_hi = min >> lb;
    let offs = vals
        .iter()
        .map(|&v| (v - ((base_hi) << lb)) as u32)
        .collect();
    Some((Side::Prog { base_hi, lb }, offs))
}

/// Group gates/consts of one layer into verified closed-form families plus
/// the exact sparse remainder.
///
/// FV-CONTRACT (Creusot, R2 - design contract, NOT tool-checked): the
/// exact-repartition property - expanding the derived groups plus the
/// sparse remainder reproduces the layer's gate/const lists AS
/// MULTISETS. This is the premise of `Wiring_MLE.derived_mle_eq_table`
/// (lemma (c), D-38): repartition + field re-association forces the
/// derived oracle to equal the table oracle AT EVERY POINT. Executable
/// pin: tests/verify_succinct.rs (exact repartition + bit-identical
/// equality); the polynomial identity itself is discharged on the model
/// side.
/// TOOL WALL (R2 dev; `#[trusted]` = translation opt-out, ZERO claims):
/// the grouping walks `BTreeMap` iterators, whose `IteratorSpec`
/// instances creusot-std lacks - a hard translation error (E0277), the
/// same missing-iterator-spec class as R1's `BTreeMap` wall
/// (`Builder::build_with_hints`) and wall 1 (`unzip`).
#[cfg_attr(creusot, trusted)]
fn derive_layer(
    layer: &Layer<BaseField>,
    hints: &LayerHints,
    out_bits: usize,
    in_bits: usize,
) -> DerivedLayer {
    let mut sparse_gates: Vec<Gate<BaseField>> = Vec::new();
    let mut sparse_consts: Vec<(u32, BaseField)> = Vec::new();

    // Partition gate indices by (family, block). Untagged -> sparse.
    let mut fams: BTreeMap<u32, BTreeMap<u32, Vec<usize>>> = BTreeMap::new();
    for (gi, g) in layer.gates.iter().enumerate() {
        match hints.gates.get(gi).copied().flatten() {
            Some(tag) => fams
                .entry(tag.family)
                .or_default()
                .entry(tag.block)
                .or_default()
                .push(gi),
            None => sparse_gates.push(*g),
        }
    }

    // Groups keyed by (block count, side progressions); the count in the
    // key keeps distinct families with coincidentally equal sides but
    // different block counts apart. (BTreeMap: deterministic layout.)
    let mut groups: BTreeMap<(u64, Side, Side, Side), GateGroup> = BTreeMap::new();
    let mut push_tap =
        |key: (u64, Side, Side, Side), g: &Gate<BaseField>, offs: (u32, u32, u32)| {
            let e = groups.entry(key).or_insert_with(|| GateGroup {
                count: key.0,
                out: key.1,
                in1: key.2,
                in2: key.3,
                lin: Vec::new(),
                pow3: Vec::new(),
                mul: Vec::new(),
            });
            match g.kind {
                GateKind::Lin => e.lin.push((offs.0, offs.1, g.coeff)),
                GateKind::Pow3 => e.pow3.push((offs.0, offs.1, g.coeff)),
                GateKind::Mul => e.mul.push((offs.0, offs.1, offs.2, g.coeff)),
            }
        };

    for blocks in fams.into_values() {
        let ids: Vec<u32> = blocks.keys().copied().collect();
        let per_block: Vec<&Vec<usize>> = blocks.values().collect();
        let consecutive = ids.windows(2).all(|w| w[1] == w[0] + 1);
        let uniform_len = per_block.iter().all(|v| v.len() == per_block[0].len());
        if !consecutive || !uniform_len {
            for v in &per_block {
                for &gi in *v {
                    sparse_gates.push(layer.gates[gi]);
                }
            }
            continue;
        }
        let c = per_block.len() as u64;

        if c == 1 {
            // Single block: fit each side as one aligned window over the
            // whole template, split unary/binary so Mul's in2 fit does not
            // widen the unary window.
            for is_mul in [false, true] {
                let gs: Vec<Gate<BaseField>> = per_block[0]
                    .iter()
                    .map(|&gi| layer.gates[gi])
                    .filter(|g| matches!(g.kind, GateKind::Mul) == is_mul)
                    .collect();
                if gs.is_empty() {
                    continue;
                }
                let outs: Vec<u64> = gs.iter().map(|g| g.out as u64).collect();
                let in1s: Vec<u64> = gs.iter().map(|g| g.in1 as u64).collect();
                let in2s: Vec<u64> = gs.iter().map(|g| g.in2 as u64).collect();
                match (fit_window(&outs), fit_window(&in1s), fit_window(&in2s)) {
                    (Some((so, oo)), Some((s1, o1)), Some((s2, o2))) => {
                        for (i, g) in gs.iter().enumerate() {
                            push_tap((1, so, s1, s2), g, (oo[i], o1[i], o2[i]));
                        }
                    }
                    _ => sparse_gates.extend(gs),
                }
            }
            continue;
        }

        // Multi-block: fit every template SLOT independently across blocks
        // (slot = same creation-order position in every block), then group
        // slots that share the same three side progressions under one block
        // factor. Kind and coefficient must be block-uniform per slot.
        for s in 0..per_block[0].len() {
            let gs: Vec<Gate<BaseField>> = per_block.iter().map(|pb| layer.gates[pb[s]]).collect();
            let uniform = gs
                .iter()
                .all(|g| g.kind == gs[0].kind && g.coeff == gs[0].coeff);
            let outs: Vec<u64> = gs.iter().map(|g| g.out as u64).collect();
            let in1s: Vec<u64> = gs.iter().map(|g| g.in1 as u64).collect();
            let in2s: Vec<u64> = gs.iter().map(|g| g.in2 as u64).collect();
            let fitted = if uniform {
                match (
                    fit_progression(&outs),
                    fit_progression(&in1s),
                    fit_progression(&in2s),
                ) {
                    (Some((so, oo)), Some((s1, o1)), Some((s2, o2))) => {
                        Some(((so, s1, s2), (oo, o1, o2)))
                    }
                    _ => None,
                }
            } else {
                None
            };
            match fitted {
                Some(((so, s1, s2), offs)) => push_tap((c, so, s1, s2), &gs[0], offs),
                None => sparse_gates.extend(gs),
            }
        }
    }

    // Constants: same scheme, with block-uniform VALUES required.
    let mut cfams: BTreeMap<u32, BTreeMap<u32, Vec<usize>>> = BTreeMap::new();
    for (ci, &(w, v)) in layer.consts.iter().enumerate() {
        match hints.consts.get(ci).copied().flatten() {
            Some(tag) => cfams
                .entry(tag.family)
                .or_default()
                .entry(tag.block)
                .or_default()
                .push(ci),
            None => sparse_consts.push((w, v)),
        }
    }
    let mut const_groups: BTreeMap<(u64, Side), ConstGroup> = BTreeMap::new();
    for blocks in cfams.into_values() {
        let ids: Vec<u32> = blocks.keys().copied().collect();
        let per_block: Vec<&Vec<usize>> = blocks.values().collect();
        let consecutive = ids.windows(2).all(|w| w[1] == w[0] + 1);
        let uniform_len = per_block.iter().all(|v| v.len() == per_block[0].len());
        if !consecutive || !uniform_len {
            for v in &per_block {
                for &ci in *v {
                    sparse_consts.push(layer.consts[ci]);
                }
            }
            continue;
        }
        let c = per_block.len() as u64;
        if c == 1 {
            let cs: Vec<(u32, BaseField)> =
                per_block[0].iter().map(|&ci| layer.consts[ci]).collect();
            let outs: Vec<u64> = cs.iter().map(|&(w, _)| w as u64).collect();
            match fit_window(&outs) {
                Some((so, oo)) => {
                    let e = const_groups.entry((1, so)).or_insert_with(|| ConstGroup {
                        count: 1,
                        out: so,
                        vals: Vec::new(),
                    });
                    for (i, &(_, v)) in cs.iter().enumerate() {
                        e.vals.push((oo[i], v));
                    }
                }
                None => sparse_consts.extend(cs),
            }
            continue;
        }
        for s in 0..per_block[0].len() {
            let cs: Vec<(u32, BaseField)> =
                per_block.iter().map(|pb| layer.consts[pb[s]]).collect();
            let uniform_val = cs.iter().all(|&(_, v)| v == cs[0].1);
            let outs: Vec<u64> = cs.iter().map(|&(w, _)| w as u64).collect();
            match (uniform_val, fit_progression(&outs)) {
                (true, Some((so, oo))) => {
                    let e = const_groups.entry((c, so)).or_insert_with(|| ConstGroup {
                        count: c,
                        out: so,
                        vals: Vec::new(),
                    });
                    e.vals.push((oo, cs[0].1));
                }
                _ => sparse_consts.extend(cs),
            }
        }
    }

    DerivedLayer {
        groups: groups.into_values().collect(),
        sparse_gates,
        const_groups: const_groups.into_values().collect(),
        sparse_consts,
        out_bits,
        in_bits,
    }
}

/// Split a point at a side's local width and return `(hi, lo_table)`.
fn split_side(point: &[ChallengeField], side: Side) -> (&[ChallengeField], Vec<ChallengeField>) {
    let lb = side.lb() as usize;
    debug_assert!(lb <= point.len(), "side wider than the point");
    let (hi, lo) = point.split_at(point.len() - lb);
    (hi, eq_table(lo))
}

impl WiringOracle<ChallengeField> for DerivedRegularWiring {
    /// Logical view of the derived-layer count (S-3 seal extension -
    /// see the trait). The width methods restate the trait requires (no
    /// inheritance at this rev); the two eval methods stay `#[trusted]`
    /// translation opt-outs (walls 4/5) and need no restatement - call
    /// sites are governed by the trait contract either way.
    #[cfg(creusot)]
    #[logic]
    fn n_layers(self) -> Int {
        pearlite! { self.layers@.len() }
    }

    #[cfg_attr(creusot, requires(layer@ < self.n_layers()))]
    fn out_width_bits(&self, layer: usize) -> usize {
        self.layers[layer].out_bits
    }

    #[cfg_attr(creusot, requires(layer@ < self.n_layers()))]
    fn in_width_bits(&self, layer: usize) -> usize {
        self.layers[layer].in_bits
    }

    /// TOOL WALL (R2 dev; `#[trusted]` = translation opt-out, ZERO
    /// claims): field-element compares + foreign-const `ZERO`/`ONE`
    /// (the `DeepModel`/foreign-const walls). Semantics held by
    /// `Wiring_MLE.derived_eval` + `derived_mle_eq_table` (model) and
    /// the bit-identical equality pins (tests/verify_succinct.rs).
    #[cfg_attr(creusot, trusted)]
    fn eval_predicate_mle(
        &self,
        layer: usize,
        kind: GateKind,
        z: &[ChallengeField],
        x: &[ChallengeField],
        y: &[ChallengeField],
    ) -> ChallengeField {
        let lay = &self.layers[layer];
        let is_mul = matches!(kind, GateKind::Mul);
        let mut acc = ChallengeField::ZERO;

        for grp in &lay.groups {
            let empty = match kind {
                GateKind::Lin => grp.lin.is_empty(),
                GateKind::Pow3 => grp.pow3.is_empty(),
                GateKind::Mul => grp.mul.is_empty(),
            };
            if empty {
                continue;
            }
            // Block factor D: shifted-range eq over the progression sides,
            // times point-eq scalars for fixed sides. Unary predicates live
            // on (z, x) only.
            let mut scalar = ChallengeField::ONE;
            let mut terms: Vec<(&[ChallengeField], u64)> = Vec::with_capacity(3);
            let (z_hi, zt) = split_side(z, grp.out);
            let (x_hi, xt) = split_side(x, grp.in1);
            match grp.out {
                Side::Prog { base_hi, .. } => terms.push((z_hi, base_hi)),
                Side::Fixed { wire } => scalar *= eq_point_index(z, wire as usize),
            }
            match grp.in1 {
                Side::Prog { base_hi, .. } => terms.push((x_hi, base_hi)),
                Side::Fixed { wire } => scalar *= eq_point_index(x, wire as usize),
            }
            let yt = if is_mul {
                let (y_hi, yt) = split_side(y, grp.in2);
                match grp.in2 {
                    Side::Prog { base_hi, .. } => terms.push((y_hi, base_hi)),
                    Side::Fixed { wire } => scalar *= eq_point_index(y, wire as usize),
                }
                yt
            } else {
                Vec::new()
            };
            let d = scalar * shifted_range_eq(&terms, grp.count);
            if d == ChallengeField::ZERO {
                continue;
            }
            // Local template sum T over the tap offsets.
            let mut t = ChallengeField::ZERO;
            match kind {
                GateKind::Lin => {
                    for &(o, i1, coeff) in &grp.lin {
                        t += embed(coeff) * zt[o as usize] * xt[i1 as usize];
                    }
                }
                GateKind::Pow3 => {
                    for &(o, i1, coeff) in &grp.pow3 {
                        t += embed(coeff) * zt[o as usize] * xt[i1 as usize];
                    }
                }
                GateKind::Mul => {
                    for &(o, i1, i2, coeff) in &grp.mul {
                        t += embed(coeff) * zt[o as usize] * xt[i1 as usize] * yt[i2 as usize];
                    }
                }
            }
            acc += d * t;
        }

        // Exact sparse remainder (same per-gate terms as TableWiring).
        for g in &lay.sparse_gates {
            if g.kind != kind {
                continue;
            }
            let mut term = embed(g.coeff)
                * eq_point_index(z, g.out as usize)
                * eq_point_index(x, g.in1 as usize);
            if is_mul {
                term *= eq_point_index(y, g.in2 as usize);
            }
            acc += term;
        }
        acc
    }

    /// TOOL WALL (R2 dev; `#[trusted]` = translation opt-out, ZERO
    /// claims): same walls as `eval_predicate_mle`. Semantics held by
    /// `Wiring_MLE.derived_const_eval` + `derived_const_mle_eq_table`.
    #[cfg_attr(creusot, trusted)]
    fn eval_const_mle(&self, layer: usize, z: &[ChallengeField]) -> ChallengeField {
        let lay = &self.layers[layer];
        let mut acc = ChallengeField::ZERO;
        for grp in &lay.const_groups {
            let (z_hi, zt) = split_side(z, grp.out);
            let d = match grp.out {
                Side::Prog { base_hi, .. } => shifted_range_eq(&[(z_hi, base_hi)], grp.count),
                Side::Fixed { wire } => eq_point_index(z, wire as usize),
            };
            if d == ChallengeField::ZERO {
                continue;
            }
            let mut t = ChallengeField::ZERO;
            for &(o, v) in &grp.vals {
                t += embed(v) * zt[o as usize];
            }
            acc += d * t;
        }
        for &(w, v) in &lay.sparse_consts {
            acc += embed(v) * eq_point_index(z, w as usize);
        }
        acc
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;
    use crate::circuit::evaluate_circuit;
    use crate::mle::mle_eval_base;
    use ssgkr_primitives::Transcript;

    fn bf(x: u32) -> BaseField {
        BaseField::from_u32(x)
    }
    fn cf(x: u32) -> ChallengeField {
        ChallengeField::from(BaseField::from_u32(x))
    }
    fn ug(kind: GateKind, out: u32, in1: u32) -> LocalGate {
        LocalGate {
            kind,
            out,
            in1,
            in2: in1,
            coeff: BaseField::ONE,
        }
    }

    /// A two-level data-parallel circuit (2 blocks), exercising Lin, Mul,
    /// Pow3 and a per-block constant.
    fn regular() -> RegularWiring {
        RegularWiring {
            layers: vec![
                // Output layer: [in0^3 + 5, in1]
                RegularLayer {
                    copy_bits: 1,
                    out_local_bits: 1,
                    in_local_bits: 1,
                    gates: vec![ug(GateKind::Pow3, 0, 0), ug(GateKind::Lin, 1, 1)],
                    consts: vec![(0, bf(5))],
                },
                // Deepest layer: [in0 + in1, in0 * in1]
                RegularLayer {
                    copy_bits: 1,
                    out_local_bits: 1,
                    in_local_bits: 1,
                    gates: vec![
                        ug(GateKind::Lin, 0, 0),
                        ug(GateKind::Lin, 0, 1),
                        LocalGate {
                            kind: GateKind::Mul,
                            out: 1,
                            in1: 0,
                            in2: 1,
                            coeff: BaseField::ONE,
                        },
                    ],
                    consts: vec![],
                },
            ],
        }
    }

    fn rand_point(len: usize, seed: u32) -> Vec<ChallengeField> {
        (0..len)
            .map(|i| {
                cf(seed
                    .wrapping_mul(2654435761)
                    .wrapping_add(i as u32 * 40503 + 7)
                    % 2000)
            })
            .collect()
    }

    #[test]
    fn closed_form_matches_materialized_table() {
        let reg = regular();
        let circuit = reg.materialize();
        let table = TableWiring::new(&circuit);

        for layer in 0..circuit.layers.len() {
            let ob = WiringOracle::<ChallengeField>::out_width_bits(&reg, layer);
            let ib = WiringOracle::<ChallengeField>::in_width_bits(&reg, layer);
            assert_eq!(ob, table.out_width_bits(layer));
            assert_eq!(ib, table.in_width_bits(layer));
            for s in 0..4u32 {
                let z = rand_point(ob, s + 1);
                let x = rand_point(ib, s + 11);
                let y = rand_point(ib, s + 23);
                for kind in [GateKind::Lin, GateKind::Mul, GateKind::Pow3] {
                    assert_eq!(
                        reg.eval_predicate_mle(layer, kind, &z, &x, &y),
                        table.eval_predicate_mle(layer, kind, &z, &x, &y),
                        "predicate {kind:?} layer {layer} seed {s}"
                    );
                }
                assert_eq!(
                    reg.eval_const_mle(layer, &z),
                    table.eval_const_mle(layer, &z),
                    "const layer {layer} seed {s}"
                );
            }
        }
    }

    #[test]
    fn prove_verifies_under_both_oracles() {
        const TAG: &[u8] = b"regular-wiring-test";
        let reg = regular();
        let circuit = reg.materialize();
        let inputs = [bf(2), bf(3), bf(4), bf(5)];
        let witness = evaluate_circuit(&circuit, &inputs).unwrap();
        let outputs = witness.layer_values[0].clone();

        let mut t = Transcript::new(TAG);
        t.observe_many(&outputs);
        let proof = crate::prove(&circuit, &witness, &mut t);

        // The succinct closed-form oracle and the materialized table oracle
        // must yield the identical verification result and residual claim.
        let table = TableWiring::new(&circuit);
        let mut tr = Transcript::new(TAG);
        tr.observe_many(&outputs);
        let reg_claim = crate::verify(&circuit, &reg, &outputs, &proof, &mut tr).unwrap();
        let mut tt = Transcript::new(TAG);
        tt.observe_many(&outputs);
        let table_claim = crate::verify(&circuit, &table, &outputs, &proof, &mut tt).unwrap();
        assert_eq!(reg_claim, table_claim);

        // And the residual input claim discharges against the real inputs.
        assert_eq!(
            mle_eval_base(&inputs, &reg_claim.point),
            reg_claim.expected_eval
        );
        assert_eq!(
            mle_eval_base(&inputs, &reg_claim.point_y),
            reg_claim.expected_eval_y
        );
    }

    // -- derived closed-form machinery ------------------------------------

    /// The carry-DP shifted-range eq equals the brute-force sum for random
    /// points/bases/counts, including the degenerate edges (count 0, count
    /// 1, empty terms, full power-of-two ranges == eq_points/eq3_points).
    #[test]
    fn shifted_range_eq_matches_bruteforce() {
        let brute = |terms: &[(&[ChallengeField], u64)], count: u64| -> ChallengeField {
            let mut acc = ChallengeField::ZERO;
            for b in 0..count {
                let mut w = ChallengeField::ONE;
                for &(p, base) in terms {
                    w *= eq_point_index(p, (base + b) as usize);
                }
                acc += w;
            }
            acc
        };
        for seed in 0..6u32 {
            let p6 = rand_point(6, seed + 1);
            let p8 = rand_point(8, seed + 41);
            let p10 = rand_point(10, seed + 97);
            for &count in &[0u64, 1, 2, 3, 5, 8, 24, 31, 47] {
                // One, two and three terms with mixed lengths and bases.
                let cases: Vec<Vec<(&[ChallengeField], u64)>> = vec![
                    vec![(&p6, 5)],
                    vec![(&p6, 3), (&p10, 900)],
                    vec![(&p8, 17), (&p8, 128), (&p10, 64)],
                ];
                for terms in cases {
                    if terms
                        .iter()
                        .any(|&(p, base)| base + count > (1u64 << p.len()))
                    {
                        continue;
                    }
                    assert_eq!(
                        shifted_range_eq(&terms, count),
                        brute(&terms, count),
                        "seed {seed} count {count}"
                    );
                }
            }
            // Full-range diagonals reduce to the uniform-block identities.
            let q6 = rand_point(6, seed + 71);
            let r6 = rand_point(6, seed + 83);
            assert_eq!(
                shifted_range_eq(&[(&p6, 0), (&q6, 0)], 64),
                eq_points(&p6, &q6)
            );
            assert_eq!(
                shifted_range_eq(&[(&p6, 0), (&q6, 0), (&r6, 0)], 64),
                eq3_points(&p6, &q6, &r6)
            );
            // Empty terms: the sum of empty products is `count`.
            assert_eq!(
                shifted_range_eq(&[], 13),
                ChallengeField::from(BaseField::from_u32(13))
            );
        }
    }

    /// `eq_table` agrees with `eq_point_index` entry-by-entry.
    #[test]
    fn eq_table_matches_pointwise_eq() {
        let p = rand_point(5, 9);
        let t = eq_table(&p);
        assert_eq!(t.len(), 32);
        for (idx, &e) in t.iter().enumerate() {
            assert_eq!(e, eq_point_index(&p, idx), "idx {idx}");
        }
    }

    /// Hints for a materialized regular circuit: every block's template
    /// gates/consts tagged (family 0, block b) in emission order.
    fn hints_for_materialized(reg: &RegularWiring) -> WiringHints {
        WiringHints {
            layers: reg
                .layers
                .iter()
                .map(|lay| {
                    let blocks = 1u32 << lay.copy_bits;
                    let mut gates = Vec::new();
                    let mut consts = Vec::new();
                    for b in 0..blocks {
                        let tag = Some(FamilyTag {
                            family: 0,
                            block: b,
                        });
                        gates.extend(std::iter::repeat_n(tag, lay.gates.len()));
                        consts.extend(std::iter::repeat_n(tag, lay.consts.len()));
                    }
                    LayerHints { gates, consts }
                })
                .collect(),
        }
    }

    /// The derived oracle is bit-identical to the table oracle on the same
    /// circuit - grouped (real hints), and degraded (no hints -> the exact
    /// sparse path).
    #[test]
    fn derived_wiring_matches_table_grouped_and_sparse() {
        let reg = regular();
        let circuit = reg.materialize();
        let table = TableWiring::new(&circuit);

        let grouped = DerivedRegularWiring::derive(&circuit, &hints_for_materialized(&reg));
        let stats = grouped.stats();
        assert_eq!(stats.sparse_gates, 0, "regular circuit fully grouped");
        assert!(stats.groups > 0);

        let sparse = DerivedRegularWiring::derive(&circuit, &WiringHints::default());
        assert_eq!(sparse.stats().grouped_gates, 0, "no hints -> all sparse");

        for layer in 0..circuit.layers.len() {
            let ob = table.out_width_bits(layer);
            let ib = table.in_width_bits(layer);
            assert_eq!(grouped.out_width_bits(layer), ob);
            assert_eq!(grouped.in_width_bits(layer), ib);
            for s in 0..6u32 {
                let z = rand_point(ob, s + 5);
                let x = rand_point(ib, s + 17);
                let y = rand_point(ib, s + 29);
                for kind in [GateKind::Lin, GateKind::Mul, GateKind::Pow3] {
                    let want = table.eval_predicate_mle(layer, kind, &z, &x, &y);
                    assert_eq!(
                        grouped.eval_predicate_mle(layer, kind, &z, &x, &y),
                        want,
                        "grouped {kind:?} layer {layer} seed {s}"
                    );
                    assert_eq!(
                        sparse.eval_predicate_mle(layer, kind, &z, &x, &y),
                        want,
                        "sparse {kind:?} layer {layer} seed {s}"
                    );
                }
                let wantc = table.eval_const_mle(layer, &z);
                assert_eq!(grouped.eval_const_mle(layer, &z), wantc);
                assert_eq!(sparse.eval_const_mle(layer, &z), wantc);
            }
        }
    }

    /// Wrong hints must never change results, only coverage: tag gates with
    /// a nonsense grouping (mixed blocks, non-uniform sizes) and the oracle
    /// still equals the table (everything that fails verification lands on
    /// the sparse path).
    #[test]
    fn wrong_hints_degrade_to_sparse_but_stay_correct() {
        let reg = regular();
        let circuit = reg.materialize();
        let table = TableWiring::new(&circuit);
        // Nonsense: alternate blocks 0/1 per gate index within one family
        // (breaks per-block template uniformity) and skip block ids (1, 3).
        let hints = WiringHints {
            layers: circuit
                .layers
                .iter()
                .map(|lay| LayerHints {
                    gates: (0..lay.gates.len())
                        .map(|i| {
                            Some(FamilyTag {
                                family: 7,
                                block: if i % 2 == 0 { 1 } else { 3 },
                            })
                        })
                        .collect(),
                    consts: vec![None; lay.consts.len()],
                })
                .collect(),
        };
        let derived = DerivedRegularWiring::derive(&circuit, &hints);
        for layer in 0..circuit.layers.len() {
            let ob = table.out_width_bits(layer);
            let ib = table.in_width_bits(layer);
            for s in 0..4u32 {
                let z = rand_point(ob, s + 3);
                let x = rand_point(ib, s + 13);
                let y = rand_point(ib, s + 31);
                for kind in [GateKind::Lin, GateKind::Mul, GateKind::Pow3] {
                    assert_eq!(
                        derived.eval_predicate_mle(layer, kind, &z, &x, &y),
                        table.eval_predicate_mle(layer, kind, &z, &x, &y),
                        "{kind:?} layer {layer} seed {s}"
                    );
                }
                assert_eq!(
                    derived.eval_const_mle(layer, &z),
                    table.eval_const_mle(layer, &z)
                );
            }
        }
    }
}
