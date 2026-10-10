//! Circuit structure compilation (witness-independent, cacheable).
//!
//! The compiled circuit verifies a sparse-Merkle-tree operation as a SHALLOW,
//! DATA-PARALLEL constraint system (strategy A): the running accumulators
//! `acc_0..acc_d` are witness inputs and every hash transition is checked
//! independently, so one identical sub-circuit is instantiated per tree
//! level. The circuit is key-agnostic - the left/right sibling order at each
//! level is selected by a public key-bit input via a multiplexer (`Mul`
//! gates), so one compiled circuit is reused across every key of the same op
//! kind (the Module-3 batching premise).
//!
//! Acceptance (`is_accepting`, all output wires zero) holds iff every hash
//! transition is consistent, the top accumulator equals the public root, and
//! the leaf pre-hash equals the public `value_digest`. Combined with the
//! facade's public-input checks (root relation per op kind, key bits vs
//! `asset_id`) this realizes Theorem A: `circuit_accept <=> smt_valid`.

use ssgkr_primitives::field::{BaseField, PrimeCharacteristicRing};
use ssgkr_primitives::hash::{DIGEST_WIDTH, HashRoundTemplate, LEAF_SPONGE_RATE, leaf_pre_width};
use ssgkr_primitives::poseidon2_arith as p2;
use ssgkr_protocol::{GateKind, LayeredCircuit, WiringHints};

use crate::builder::{Builder, NodeId, TapKind};
use crate::params::{LayerStrategy, SmtParams};
use crate::smt::SmtOpKind;

// Named imports on purpose (the prelude glob would shadow the std derives
// and `vec!` - see the note in ssgkr-primitives::hash).
#[cfg(creusot)]
use creusot_std::prelude::{Int, ensures, logic, pearlite, requires};

/// Creusot specifications absent from creusot-std at the pinned rev:
///
/// - `Result::map` (its `result.rs` covers `is_ok`/`unwrap`/... but not
///   `map`). Same shape as creusot-std's own `Option::map` spec: `Ok`/`Err`
///   preservation plus the closure's postcondition - the plain std behavior.
/// - `Iterator::unzip`: NO clauses on purpose - a claim-free spec whose only
///   effect is making the call ADMISSIBLE (an unspecced external function
///   carries an impossible precondition, which left `compile_with_hints`
///   at 37/39 with two open call-admissibility obligations). The result
///   stays logically unconstrained; nothing downstream consumes it in a
///   contract.
#[cfg(creusot)]
mod creusot_specs {
    use creusot_std::prelude::*;

    extern_spec! {
        impl<T, E> Result<T, E> {
            #[requires(match self { Err(_) => true, Ok(t) => f.precondition((t,)) })]
            #[ensures(match self {
                Err(e) => resolve(f) && result == Err(e),
                Ok(t) => exists<r> result == Ok(r) && f.postcondition_once((t,), r),
            })]
            fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Result<U, E> {
                match self {
                    Ok(t) => Ok(f(t)),
                    Err(e) => Err(e),
                }
            }
        }

        mod std {
            mod iter {
                trait Iterator {
                    #[allow(dead_code)]
                    fn unzip<A, B, FromA, FromB>(self) -> (FromA, FromB)
                    where
                        Self: Sized + Iterator<Item = (A, B)>,
                        FromA: Default + Extend<A>,
                        FromB: Default + Extend<B>;
                }
            }
        }
    }
}

/// Errors from circuit compilation.
///
/// (Under `--cfg creusot` the verifier's `PartialEq` derive needs a
/// `DeepModel`; the `&'static str` reason and plain indices have one, so
/// it is simply derived.)
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(creusot, derive(creusot_std::prelude::DeepModel))]
pub enum CompileError {
    /// The strategy/parameter combination is not supported in v0.1.
    UnsupportedConfig {
        /// Human-readable reason.
        reason: &'static str,
    },
    /// A `Lin`/`Pow3` gate violates the unary convention (`in2 != in1`).
    NonUnaryGate {
        /// Layer index (0 = output layer).
        layer: usize,
        /// Output wire of the offending gate.
        out: u32,
    },
}

/// Input-vector layout of a compiled SMT circuit. Shared by `compile` (which
/// creates the `Input` nodes) and `generate_witness` (which fills the values)
/// so the two never disagree on where a wire lives.
#[derive(Clone, Copy, Debug)]
pub struct InputLayout {
    /// Operation kind this layout is for.
    pub kind: SmtOpKind,
    /// Tree depth.
    pub depth: usize,
    /// Total input wires (before power-of-two padding).
    pub input_width: u32,
    /// Leaf pre-image lanes (= `leaf_pre_width(leaf_max_fields)`, an instance
    /// parameter: the CR leaf hash's fixed, lossless pre-image width).
    leaf_lanes: u32,
    leaf_pre: u32,
    acc: u32,
    sib: u32,
    key_bits: u32,
    root: u32,
    value_digest: u32,
    leaf_pre2: u32,
    acc2: u32,
    root2: u32,
    has_second: bool,
}

const W: u32 = DIGEST_WIDTH as u32; // 8
const P2W: usize = p2::P2_WIDTH; // 16 (Poseidon2 state width)

// Family-scope ids for the derived-wiring layout hints (opaque labels; the
// derivation re-verifies every grouping, see `Builder::scope`). Per-path
// families are offset by FAM_PATH_STRIDE for the Update second path.
const FAM_PATH_STRIDE: u32 = 16;
const F_SPONGE: u32 = 0;
const F_PRE_IN: u32 = 1;
const F_ACC_IN: u32 = 2;
const F_LEAF_RES: u32 = 3;
const F_SIB_IN: u32 = 4;
const F_KEY_IN: u32 = 5;
const F_MUX: u32 = 6;
const F_NODE: u32 = 7;
const F_NODE_RES: u32 = 8;
const F_ROOT_IN: u32 = 9;
const F_ROOT_RES: u32 = 10;
const F_VD_RES: u32 = 2 * FAM_PATH_STRIDE;
const F_BOOL: u32 = F_VD_RES + 1;
const F_TAG_RES: u32 = F_VD_RES + 2;

/// Opaque logic projections of the layout's PRIVATE fields - the
/// abstraction seam of the layout contracts.
///
/// Trap-13 workaround (partial-audit C / upstream-report candidate): a
/// contract that projects private fields directly (`result.acc@`) breaks
/// Creusot's codegen when the contract is CONSUMED from another module -
/// the caller's coma gets literal `ERROR_UNBOUND_<field>` tokens (a why3
/// syntax error; public fields resolve fine). Routing every private-field
/// mention through these non-`open` `#[logic]` projections keeps the
/// field access inside this module; consumers (witness.rs) see only the
/// opaque symbols plus the contract equations below.
#[cfg(creusot)]
impl InputLayout {
    /// `leaf_lanes` (= `leaf_pre_width(leaf_max_fields)`), as Int.
    #[logic]
    pub fn l_leaf_lanes(self) -> Int {
        pearlite! { self.leaf_lanes@ }
    }
    /// `leaf_pre` base offset, as Int.
    #[logic]
    pub fn l_leaf_pre(self) -> Int {
        pearlite! { self.leaf_pre@ }
    }
    /// `acc` segment base, as Int.
    #[logic]
    pub fn l_acc(self) -> Int {
        pearlite! { self.acc@ }
    }
    /// `sib` segment base, as Int.
    #[logic]
    pub fn l_sib(self) -> Int {
        pearlite! { self.sib@ }
    }
    /// `key_bits` segment base, as Int.
    #[logic]
    pub fn l_key_bits(self) -> Int {
        pearlite! { self.key_bits@ }
    }
    /// `root` base offset, as Int.
    #[logic]
    pub fn l_root(self) -> Int {
        pearlite! { self.root@ }
    }
    /// `value_digest` base offset, as Int.
    #[logic]
    pub fn l_value_digest(self) -> Int {
        pearlite! { self.value_digest@ }
    }
    /// `leaf_pre2` base offset (Update only), as Int.
    #[logic]
    pub fn l_leaf_pre2(self) -> Int {
        pearlite! { self.leaf_pre2@ }
    }
    /// `acc2` segment base (Update only), as Int.
    #[logic]
    pub fn l_acc2(self) -> Int {
        pearlite! { self.acc2@ }
    }
    /// `root2` base offset (Update only), as Int.
    #[logic]
    pub fn l_root2(self) -> Int {
        pearlite! { self.root2@ }
    }
    /// Whether the layout has the second (new-leaf) path.
    #[logic]
    pub fn l_has_second(self) -> bool {
        pearlite! { self.has_second }
    }
}

impl InputLayout {
    /// Compute the layout for an op kind, depth and leaf-encoding bound
    /// (`SmtParams::leaf_max_fields` - fixes the leaf pre-image lane count).
    ///
    /// R1 refinement anchor (Creusot-checked): the contract mirrors the
    /// Isabelle input-vector layout 1:1 (`Compiler_Model.thy`, subsection
    /// "Input-vector layout (Rust: InputLayout, same segment order)"),
    /// with the model symbols instantiated as W = 8 (`DIGEST_WIDTH`) and
    /// L = `leaf_pre_width(leaf_max_fields)` (spelled out in its
    /// quotient/remainder form, as in `Leaf_Fold.thy`):
    ///
    ///   read-only branch ~ `ro_lp`/`ro_acc`/`ro_sib`/`ro_kb`/`ro_root`/
    ///                      `ro_vd`/`ro_width`
    ///   Update branch    ~ `up_lp`/`up_lp2`/`up_acc`/`up_acc2`/`up_sib`/
    ///                      `up_kb`/`up_root`/`up_root2`/`up_vd`/`up_width`
    ///
    /// Private-field offsets are stated through the opaque projections
    /// above (trap-13 seam); the arithmetic content is unchanged. The
    /// `requires` are machine-width side conditions only (u32 segment
    /// arithmetic and lossless `as` casts; the model is over unbounded
    /// `nat`).
    #[cfg_attr(creusot, requires(depth@ <= 0xFFFF && leaf_max_fields@ <= 0xFFFF))]
    #[cfg_attr(creusot, ensures(result.kind == kind && result.depth@ == depth@))]
    #[cfg_attr(creusot, ensures(result.l_leaf_lanes()
        == ((leaf_max_fields@ + 1) / 8 + if (leaf_max_fields@ + 1) % 8 == 0 { 0 } else { 1 }) * 8))]
    #[cfg_attr(creusot, ensures(kind != SmtOpKind::Update ==> !result.l_has_second()
        && result.l_leaf_pre() == 0
        && result.l_acc() == result.l_leaf_lanes()
        && result.l_sib() == result.l_leaf_lanes() + 8 * (depth@ + 1)
        && result.l_key_bits() == result.l_leaf_lanes() + 8 * (2 * depth@ + 1)
        && result.l_root() == result.l_leaf_lanes() + 8 * (2 * depth@ + 1) + depth@
        && result.l_value_digest() == result.l_root() + 8
        && result.input_width@ == result.l_value_digest() + 8))]
    #[cfg_attr(creusot, ensures(kind == SmtOpKind::Update ==> result.l_has_second()
        && result.l_leaf_pre() == 0
        && result.l_leaf_pre2() == result.l_leaf_lanes()
        && result.l_acc() == 2 * result.l_leaf_lanes()
        && result.l_acc2() == 2 * result.l_leaf_lanes() + 8 * (depth@ + 1)
        && result.l_sib() == 2 * result.l_leaf_lanes() + 2 * 8 * (depth@ + 1)
        && result.l_key_bits() == 2 * result.l_leaf_lanes() + 8 * (3 * depth@ + 2)
        && result.l_root() == result.l_key_bits() + depth@
        && result.l_root2() == result.l_root() + 8
        && result.l_value_digest() == result.l_root2() + 8
        && result.input_width@ == result.l_value_digest() + 8))]
    pub fn new(kind: SmtOpKind, depth: usize, leaf_max_fields: usize) -> Self {
        let d = depth as u32;
        let lw = leaf_pre_width(leaf_max_fields) as u32;
        if matches!(kind, SmtOpKind::Update) {
            let leaf_pre = 0;
            let leaf_pre2 = lw;
            let acc = 2 * lw;
            let acc2 = acc + W * (d + 1);
            let sib = acc2 + W * (d + 1);
            let key_bits = sib + W * d;
            let root = key_bits + d;
            let root2 = root + W;
            let value_digest = root2 + W;
            let input_width = value_digest + W;
            Self {
                kind,
                depth,
                input_width,
                leaf_lanes: lw,
                leaf_pre,
                acc,
                sib,
                key_bits,
                root,
                value_digest,
                leaf_pre2,
                acc2,
                root2,
                has_second: true,
            }
        } else {
            let leaf_pre = 0;
            let acc = lw;
            let sib = acc + W * (d + 1);
            let key_bits = sib + W * d;
            let root = key_bits + d;
            let value_digest = root + W;
            let input_width = value_digest + W;
            Self {
                kind,
                depth,
                input_width,
                leaf_lanes: lw,
                leaf_pre,
                acc,
                sib,
                key_bits,
                root,
                value_digest,
                leaf_pre2: 0,
                acc2: 0,
                root2: 0,
                has_second: false,
            }
        }
    }

    // The accessor contracts below are the APPLICATION side of the model
    // map (`Compiler_Model.thy` layout definitions applied to a level
    // index, e.g. `ro_acc l = base + W * l` with W = 8); the base fields
    // are pinned to the model offsets by the `new` contract above, and
    // every private-field mention goes through the opaque projections
    // (trap-13 seam). The `requires` are u32 machine-width side
    // conditions only.

    /// Base wire of the (primary) leaf pre-image ([`Self::leaf_lanes`] wires).
    #[cfg_attr(creusot, ensures(result@ == self.l_leaf_pre()))]
    pub fn leaf_pre(&self) -> u32 {
        self.leaf_pre
    }
    /// Leaf pre-image lane count (`leaf_pre_width(leaf_max_fields)`).
    #[cfg_attr(creusot, ensures(result@ == self.l_leaf_lanes()))]
    pub fn leaf_lanes(&self) -> u32 {
        self.leaf_lanes
    }
    /// Base wire of accumulator `l` (`0..=depth`), `DIGEST_WIDTH` wires.
    #[cfg_attr(creusot, requires(self.l_acc() + 8 * l@ <= u32::MAX@))]
    #[cfg_attr(creusot, ensures(result@ == self.l_acc() + 8 * l@))]
    pub fn acc(&self, l: usize) -> u32 {
        self.acc + W * l as u32
    }
    /// Base wire of sibling `l` (`0..depth`), `DIGEST_WIDTH` wires.
    #[cfg_attr(creusot, requires(self.l_sib() + 8 * l@ <= u32::MAX@))]
    #[cfg_attr(creusot, ensures(result@ == self.l_sib() + 8 * l@))]
    pub fn sib(&self, l: usize) -> u32 {
        self.sib + W * l as u32
    }
    /// Wire of key bit `l` (`0..depth`).
    #[cfg_attr(creusot, requires(self.l_key_bits() + l@ <= u32::MAX@))]
    #[cfg_attr(creusot, ensures(result@ == self.l_key_bits() + l@))]
    pub fn key_bit(&self, l: usize) -> u32 {
        self.key_bits + l as u32
    }
    /// Base wire of the (primary/old) root.
    #[cfg_attr(creusot, ensures(result@ == self.l_root()))]
    pub fn root(&self) -> u32 {
        self.root
    }
    /// Base wire of `value_digest`.
    #[cfg_attr(creusot, ensures(result@ == self.l_value_digest()))]
    pub fn value_digest(&self) -> u32 {
        self.value_digest
    }
    /// Base wire of the new leaf pre-image (Update only).
    #[cfg_attr(creusot, ensures(result@ == self.l_leaf_pre2()))]
    pub fn leaf_pre2(&self) -> u32 {
        self.leaf_pre2
    }
    /// Base wire of new accumulator `l` (Update only).
    #[cfg_attr(creusot, requires(self.l_acc2() + 8 * l@ <= u32::MAX@))]
    #[cfg_attr(creusot, ensures(result@ == self.l_acc2() + 8 * l@))]
    pub fn acc2(&self, l: usize) -> u32 {
        self.acc2 + W * l as u32
    }
    /// Base wire of the new root (Update only).
    #[cfg_attr(creusot, ensures(result@ == self.l_root2()))]
    pub fn root2(&self) -> u32 {
        self.root2
    }
    /// Whether this layout has a second (new-leaf) path.
    #[cfg_attr(creusot, ensures(result == self.l_has_second()))]
    pub fn has_second(&self) -> bool {
        self.has_second
    }
}

/// The 16-wide vector with `v` in lane 0 and zero elsewhere (an internal
/// round adds its constant to lane 0 only).
fn lane0_rc(v: BaseField) -> [BaseField; P2W] {
    let mut rc = [BaseField::ZERO; P2W];
    rc[0] = v;
    rc
}

/// A pure linear layer `out[z] = sum_x m[z][x] * in[x] + rc[z]` (one affine
/// gate-set per output wire). Used for Poseidon2's initial external linear
/// layer, which folds in the first round's constant.
fn linear_layer(
    b: &mut Builder,
    state_in: &[NodeId; P2W],
    m: &[[BaseField; P2W]; P2W],
    rc: &[BaseField; P2W],
) -> [NodeId; P2W] {
    core::array::from_fn(|z| {
        let terms: Vec<(NodeId, BaseField)> = (0..P2W).map(|x| (state_in[x], m[z][x])).collect();
        b.affine(terms, rc[z])
    })
}

/// One fused Poseidon2 round as a SINGLE GKR layer:
/// `out[z] = sum_x m[z][x] * sbox(u[x]) + next_rc[z]`. `cube_all` selects the
/// external S-box (all 16 lanes cubed) vs the internal one (lane 0 cubed, the
/// other 15 pass through as linear taps). `next_rc` is the constant added
/// BEFORE the next cube - it rides here because a `Pow3` gate cubes its input
/// wire directly, so the addend must sit on the wire this layer produces.
fn fused_round(
    b: &mut Builder,
    u: &[NodeId; P2W],
    m: &[[BaseField; P2W]; P2W],
    cube_all: bool,
    next_rc: &[BaseField; P2W],
) -> [NodeId; P2W] {
    core::array::from_fn(|z| {
        let terms: Vec<(NodeId, BaseField, TapKind)> = (0..P2W)
            .map(|x| {
                let kind = if cube_all || x == 0 {
                    TapKind::Cube
                } else {
                    TapKind::Lin
                };
                (u[x], m[z][x], kind)
            })
            .collect();
        b.combine(terms, next_rc[z])
    })
}

/// Emit one full Poseidon2 (KoalaBear, width 16) permutation over 16 input
/// wires, returning the 16 output wires. Mirrors
/// `default_koalabear_poseidon2_16().permute()` GATE-FOR-GATE (cross-checked
/// against the native permutation in tests).
///
/// Schedule (from the plonky3 source): initial external linear layer `M_E`;
/// 4 external rounds (`AddRC` full, `x^3` all lanes, `M_E`); 20 internal
/// rounds (`AddRC` lane 0, `x^3` lane 0, `M_I`); 4 terminal external rounds.
/// Each round is one fused layer; the round constant added before a cube is
/// chained into the PRECEDING layer's constant vector (so this layer folds
/// the NEXT round's constant). 1 + 4 + 20 + 4 = 29 layers per permutation.
fn emit_permutation(b: &mut Builder, state_in: &[NodeId; P2W]) -> [NodeId; P2W] {
    let me = p2::external_matrix();
    let mi = p2::internal_matrix();
    let ext_init = p2::external_initial_rc();
    let ext_final = p2::external_final_rc();
    let int_rc = p2::internal_rc();

    // Initial external linear layer M_E, folding external round 0's constant.
    let mut u = linear_layer(b, state_in, &me, &ext_init[0]);

    // 4 initial external rounds (cube all lanes, matrix M_E). Each folds the
    // NEXT round's leading constant; round 3 folds internal round 0 (lane 0).
    for i in 0..p2::P2_EXTERNAL_HALF_ROUNDS {
        let next_rc = if i + 1 < p2::P2_EXTERNAL_HALF_ROUNDS {
            ext_init[i + 1]
        } else {
            lane0_rc(int_rc[0])
        };
        u = fused_round(b, &u, &me, true, &next_rc);
    }

    // 20 internal rounds (cube lane 0 only, matrix M_I). Fold the next internal
    // constant (lane 0); the last folds terminal round 0's full-width constant.
    for j in 0..p2::P2_INTERNAL_ROUNDS {
        let next_rc = if j + 1 < p2::P2_INTERNAL_ROUNDS {
            lane0_rc(int_rc[j + 1])
        } else {
            ext_final[0]
        };
        u = fused_round(b, &u, &mi, false, &next_rc);
    }

    // 4 terminal external rounds (cube all lanes, matrix M_E). The last round
    // has no successor cube, so its fused layer carries no constant.
    for k in 0..p2::P2_EXTERNAL_HALF_ROUNDS {
        let next_rc = if k + 1 < p2::P2_EXTERNAL_HALF_ROUNDS {
            ext_final[k + 1]
        } else {
            [BaseField::ZERO; P2W]
        };
        u = fused_round(b, &u, &me, true, &next_rc);
    }

    u
}

/// Build the 8-lane node hash `h_node(L, R) = perm([L || R])[0..8]`: the
/// truncated Poseidon2 permutation (mirrors `Poseidon2Gadget::compress`).
fn build_node_hash(b: &mut Builder, left: &[NodeId], right: &[NodeId]) -> Vec<NodeId> {
    let state: [NodeId; P2W] = core::array::from_fn(|i| {
        if i < DIGEST_WIDTH {
            left[i]
        } else {
            right[i - DIGEST_WIDTH]
        }
    });
    let out = emit_permutation(b, &state);
    out[..DIGEST_WIDTH].to_vec()
}

/// Build the 8-lane leaf hash from the fixed, LOSSLESS folded pre-image
/// (width = `leaf_pre_width(leaf_max_fields)`, a whole number of rate-8
/// blocks), mirroring `Poseidon2Gadget::hash_leaf_pre`: a rate-8
/// padding-free sponge in overwrite mode - for each block `i`, the rate
/// lanes are overwritten with `pre[8i..8i+8]` while the capacity lanes carry
/// the previous permutation's output (zeros for the first block), then the
/// state is permuted. Output = final state`[0..8]`. EVERY pre-image lane is
/// absorbed (no wrapping/summing - the 2d-audit CR fix).
/// `trusted` under Creusot: `chunks_exact` has no `IteratorSpec` at the
/// pinned rev, and the hash SUBCIRCUIT is abstract in the Isabelle model
/// (the R4 interface boundary) - no R1 obligation targets this body.
#[cfg_attr(creusot, creusot_std::prelude::trusted)]
fn build_leaf_hash(b: &mut Builder, pre: &[NodeId]) -> Vec<NodeId> {
    debug_assert_eq!(pre.len() % LEAF_SPONGE_RATE, 0);
    let zero = b.constant(BaseField::ZERO);
    let mut state: Option<[NodeId; P2W]> = None;
    for chunk in pre.chunks_exact(LEAF_SPONGE_RATE) {
        let block: [NodeId; P2W] = core::array::from_fn(|i| {
            if i < LEAF_SPONGE_RATE {
                chunk[i] // overwrite the rate lanes
            } else {
                match &state {
                    Some(s) => s[i], // capacity carried from the previous perm
                    None => zero,    // initial all-zero state
                }
            }
        });
        state = Some(emit_permutation(b, &block));
    }
    // pre is non-empty (>= one rate block), so state is always Some here;
    // fall back to zeros only to keep this total without a panic path.
    match state {
        Some(s) => s[..DIGEST_WIDTH].to_vec(),
        None => vec![zero; DIGEST_WIDTH],
    }
}

/// Key-bit multiplexer selecting the compress order (matches
/// `MerklePath::compute_root`): bit 0 -> (acc, sib), bit 1 -> (sib, acc).
///
/// `left[i]  = acc[i] + s * (sib[i] - acc[i])`,
/// `right[i] = sib[i] + s * (acc[i] - sib[i])`.
fn build_mux(
    b: &mut Builder,
    s: NodeId,
    acc: &[NodeId],
    sib: &[NodeId],
) -> (Vec<NodeId>, Vec<NodeId>) {
    let mut left = Vec::with_capacity(DIGEST_WIDTH);
    let mut right = Vec::with_capacity(DIGEST_WIDTH);
    for i in 0..DIGEST_WIDTH {
        let d_sa = b.sub(sib[i], acc[i]);
        let d_as = b.sub(acc[i], sib[i]);
        let sl = b.mul(s, d_sa);
        let sr = b.mul(s, d_as);
        left.push(b.sum(&[acc[i], sl]));
        right.push(b.sum(&[sib[i], sr]));
    }
    (left, right)
}

/// One authentication path as constraint residuals: leaf-hash binding,
/// per-level compression transitions (with key-bit mux), and the top
/// accumulator vs the given root. Appends residual nodes to `outputs`.
///
/// `fam` is the path's family-id base for the layout scopes: one family per
/// data-parallel construction site, the tree level (or digest lane) as the
/// block index, so the derived wiring can factor each site's block eq.
#[allow(clippy::too_many_arguments)]
fn build_path(
    b: &mut Builder,
    layout: &InputLayout,
    leaf_pre_base: u32,
    acc_base: impl Fn(usize) -> u32,
    root_base: u32,
    fam: u32,
    outputs: &mut Vec<NodeId>,
) {
    let d = layout.depth;
    // Inputs for this path (tags matter for the carry copies lifted off
    // them: a carried input stays in its family's window at every level).
    let leaf_pre: Vec<NodeId> = (0..layout.leaf_lanes())
        .map(|j| {
            b.scope(fam + F_PRE_IN, j);
            b.input(leaf_pre_base + j)
        })
        .collect();
    let acc: Vec<Vec<NodeId>> = (0..=d)
        .map(|l| {
            b.scope(fam + F_ACC_IN, l as u32);
            (0..W).map(|i| b.input(acc_base(l) + i)).collect()
        })
        .collect();

    // r_leaf = h_leaf(leaf_pre) - acc_0
    b.scope(fam + F_SPONGE, 0);
    let leaf_hash = build_leaf_hash(b, &leaf_pre);
    for i in 0..DIGEST_WIDTH {
        b.scope(fam + F_LEAF_RES, i as u32);
        let r = b.sub(leaf_hash[i], acc[0][i]);
        outputs.push(r);
    }

    // r_node_l = h_node(mux(acc_l, sib_l, key_l)) - acc_{l+1}
    for l in 0..d {
        b.scope(fam + F_SIB_IN, l as u32);
        let sib: Vec<NodeId> = (0..W).map(|i| b.input(layout.sib(l) + i)).collect();
        b.scope(fam + F_KEY_IN, l as u32);
        let s = b.input(layout.key_bit(l));
        b.scope(fam + F_MUX, l as u32);
        let (left, right) = build_mux(b, s, &acc[l], &sib);
        b.scope(fam + F_NODE, l as u32);
        let node_hash = build_node_hash(b, &left, &right);
        b.scope(fam + F_NODE_RES, l as u32);
        for i in 0..DIGEST_WIDTH {
            let r = b.sub(node_hash[i], acc[l + 1][i]);
            outputs.push(r);
        }
    }

    // r_root = acc_d - root
    let root: Vec<NodeId> = (0..W)
        .map(|i| {
            b.scope(fam + F_ROOT_IN, i);
            b.input(root_base + i)
        })
        .collect();
    for i in 0..DIGEST_WIDTH {
        b.scope(fam + F_ROOT_RES, i as u32);
        let r = b.sub(acc[d][i], root[i]);
        outputs.push(r);
    }
    b.unscope();
}

/// Compile the verification circuit for an operation KIND.
///
/// Circuit structure depends ONLY on `(params.depth, kind, strategy)`, never
/// on a concrete witness, so one compiled circuit is reused across a whole
/// batch (Module 3 premise). Only strategy A is implemented in v0.1.
///
/// R1 refinement anchor (Creusot-checked): the DOMAIN half of the
/// FV-CONTRACT - see [`compile_with_hints`] for the model correspondence
/// (this wrapper only drops the hints). Shape determinism ("depth and
/// widths determined by `(params.depth, kind)`") is the remaining R1
/// obligation; it needs a builder contract (currently `trusted`).
#[cfg_attr(creusot, requires(params.depth@ <= 0xFFFF && params.leaf_max_fields@ <= 0xFFFF))]
#[cfg_attr(creusot, ensures(
    (strategy == LayerStrategy::A && params.depth@ >= 1 && params.leaf_max_fields@ >= 10)
    ==> exists<c: LayeredCircuit<BaseField>> result == Ok(c)))]
#[cfg_attr(creusot, ensures(
    !(strategy == LayerStrategy::A && params.depth@ >= 1 && params.leaf_max_fields@ >= 10)
    ==> !(exists<c: LayeredCircuit<BaseField>> result == Ok(c))))]
pub fn compile(
    params: &SmtParams,
    kind: SmtOpKind,
    strategy: LayerStrategy,
    template: &HashRoundTemplate,
) -> Result<LayeredCircuit<BaseField>, CompileError> {
    compile_with_hints(params, kind, strategy, template).map(|(circuit, _)| circuit)
}

/// [`compile`] plus the layout hints for the derived closed-form wiring
/// oracle (the succinct verifier path: `DerivedRegularWiring::derive`).
/// Same canonical circuit - `compile` is this function minus the hints.
///
/// R1 refinement anchor (Creusot-checked): the DOMAIN contract mirrors the
/// modeled fragment of `Compiler_Model.thy` - the model formalizes exactly
/// strategy A over a positive tree depth, and its leaf representation
/// (`leaf_repr` ~ `Leaf_Fold.thy`, domain premise
/// `1 <= length enc <= leaf_max_fields`) must admit every leaf state (a
/// minimal Occupied encoding is 1 tag + 9 keccak limbs = 10 lanes). The
/// contract pins that compilation succeeds EXACTLY on this modeled
/// fragment: nothing outside it (unmodeled strategy, degenerate depth, an
/// Occupied-excluding bound) is silently compiled. The `requires` are
/// machine-width side conditions only (u32 segment arithmetic; the model
/// is over unbounded `nat`).
#[cfg_attr(creusot, requires(params.depth@ <= 0xFFFF && params.leaf_max_fields@ <= 0xFFFF))]
#[cfg_attr(creusot, ensures(
    (strategy == LayerStrategy::A && params.depth@ >= 1 && params.leaf_max_fields@ >= 10)
    ==> exists<c: LayeredCircuit<BaseField>, h: WiringHints> result == Ok((c, h))))]
#[cfg_attr(creusot, ensures(
    !(strategy == LayerStrategy::A && params.depth@ >= 1 && params.leaf_max_fields@ >= 10)
    ==> !(exists<c: LayeredCircuit<BaseField>, h: WiringHints> result == Ok((c, h)))))]
pub fn compile_with_hints(
    params: &SmtParams,
    kind: SmtOpKind,
    strategy: LayerStrategy,
    _template: &HashRoundTemplate,
) -> Result<(LayeredCircuit<BaseField>, WiringHints), CompileError> {
    if !matches!(strategy, LayerStrategy::A) {
        return Err(CompileError::UnsupportedConfig {
            reason: "v0.1 implements strategy A (one data-parallel instance per tree level) only",
        });
    }
    if params.depth == 0 {
        return Err(CompileError::UnsupportedConfig {
            reason: "tree depth must be positive",
        });
    }
    // The structural leaf-encoding bound must at least admit every leaf
    // state: a minimal Occupied encoding is 1 tag + 0 sync fields + 9 keccak
    // limbs = 10 elements. A smaller bound would make every Occupied leaf
    // unhashable (config foot-gun, N2).
    if params.leaf_max_fields < 10 {
        return Err(CompileError::UnsupportedConfig {
            reason: "leaf_max_fields must be >= 10 (tag + 9 keccak limbs)",
        });
    }

    let layout = InputLayout::new(kind, params.depth as usize, params.leaf_max_fields as usize);
    let mut b = Builder::new(layout.input_width);
    let mut outputs = Vec::new();

    // Primary (Membership/NonMembership leaf, or Update old leaf) path.
    build_path(
        &mut b,
        &layout,
        layout.leaf_pre(),
        |l| layout.acc(l),
        layout.root(),
        0,
        &mut outputs,
    );

    if layout.has_second() {
        // Update: the new-leaf path over the SAME siblings + key bits, bound
        // to the new root. value_digest binds the NEW leaf (S-6).
        build_path(
            &mut b,
            &layout,
            layout.leaf_pre2(),
            |l| layout.acc2(l),
            layout.root2(),
            FAM_PATH_STRIDE,
            &mut outputs,
        );
        // r_vd = acc2_0 - value_digest (new leaf pre-hash).
        let (acc2_0, vd): (Vec<NodeId>, Vec<NodeId>) = (0..W)
            .map(|i| {
                b.scope(F_VD_RES, i);
                (
                    b.input(layout.acc2(0) + i),
                    b.input(layout.value_digest() + i),
                )
            })
            .unzip();
        for i in 0..DIGEST_WIDTH {
            b.scope(F_VD_RES, i as u32);
            let r = b.sub(acc2_0[i], vd[i]);
            outputs.push(r);
        }
    } else {
        // Read-only ops: value_digest binds the (only) leaf.
        let (acc0, vd): (Vec<NodeId>, Vec<NodeId>) = (0..W)
            .map(|i| {
                b.scope(F_VD_RES, i);
                (
                    b.input(layout.acc(0) + i),
                    b.input(layout.value_digest() + i),
                )
            })
            .unzip();
        for i in 0..DIGEST_WIDTH {
            b.scope(F_VD_RES, i as u32);
            let r = b.sub(acc0[i], vd[i]);
            outputs.push(r);
        }
    }

    // [2b Finding-3, N2 defense-in-depth] Constrain every key-bit selector to
    // be boolean IN THE CIRCUIT: residual `s*(s-1) = 0`. Without it a
    // non-boolean `s` turns the level mux into an arbitrary affine blend, so a
    // self-consistent chain no boolean key could produce would be accepted -
    // latent today (inputs reconstruct `s` from the public key) but live the
    // moment a succinct/PCS verifier or witness-sourced selector is used. This
    // makes Theorem A hold circuit-intrinsically over raw input vectors.
    for l in 0..params.depth as usize {
        b.scope(F_BOOL, l as u32);
        let s = b.input(layout.key_bit(l));
        let sq = b.mul(s, s);
        let resid = b.sub(sq, s); // s^2 - s = s(s-1)
        outputs.push(resid);
    }

    // [2b Finding-1, N2 soundness, CRITICAL] NonMembership: the authenticated
    // leaf must be Empty (tag 0) or Tombstone (tag 2), never Occupied (tag 1).
    // Enforce it IN THE CIRCUIT (not just the facade) via `tag*(tag-2) = 0`,
    // whose roots are exactly {0, 2}. The tag is `leaf_pre[0]` - the fold
    // reserves lane 0 for the encoding tag UNCONDITIONALLY (R2-1 domain
    // separation, preserved by the lossless length-bound fold of the 2d CR
    // fix), so this residual is a genuine tag check at every encoding length.
    // This closes the pure-logic gap where an Occupied leaf + valid path forged
    // a non-membership proof; combined with the leaf-hash and root bindings the
    // circuit now rejects that forgery independently of hash strength.
    if matches!(kind, SmtOpKind::NonMembership) {
        b.scope(F_TAG_RES, 0);
        let tag = b.input(layout.leaf_pre());
        let sq = b.mul(tag, tag);
        let two_tag = b.affine(vec![(tag, BaseField::TWO)], BaseField::ZERO);
        let resid = b.sub(sq, two_tag); // tag^2 - 2*tag = tag(tag-2)
        outputs.push(resid);
    }
    b.unscope();

    Ok(b.build_with_hints(&outputs))
}

/// Validate the S-3 unary convention: every `Lin`/`Pow3` gate must have
/// `in2 == in1` (only `Mul` is genuinely binary). Runs in `O(#gates)`.
pub fn validate_unary_gates(circuit: &LayeredCircuit<BaseField>) -> Result<(), CompileError> {
    for (li, layer) in circuit.layers.iter().enumerate() {
        for g in &layer.gates {
            if matches!(g.kind, GateKind::Lin | GateKind::Pow3) && g.in1 != g.in2 {
                return Err(CompileError::NonUnaryGate {
                    layer: li,
                    out: g.out,
                });
            }
        }
    }
    Ok(())
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;
    use crate::is_accepting;
    use crate::smt::{
        AssetId, LeafPayload, LeafState, MerklePath, SmtOperation, SmtWitness, smt_valid_native,
    };
    use crate::witness::{PublicInputs, generate_witness};
    use ssgkr_primitives::hash::{
        DEFAULT_LEAF_MAX_FIELDS, Digest, HashGadget, Poseidon2Gadget, leaf_fold,
    };
    use ssgkr_protocol::evaluate_circuit;

    fn f(x: u32) -> BaseField {
        BaseField::from_u32(x)
    }

    fn siblings(depth: usize) -> Vec<Digest<BaseField>> {
        (0..depth)
            .map(|i| Digest([f(i as u32 * 13 + 1); DIGEST_WIDTH]))
            .collect()
    }

    fn circuit_accepts(
        params: &SmtParams,
        op: &SmtOperation,
        pi: &PublicInputs,
        w: &SmtWitness,
    ) -> bool {
        let template = Poseidon2Gadget::default().round_template();
        let circuit = compile(params, op.kind(), LayerStrategy::A, &template).unwrap();
        validate_unary_gates(&circuit).expect("only the mux uses Mul; the rest is unary");
        let cw = generate_witness(params, LayerStrategy::A, &circuit, op, pi, w).unwrap();
        is_accepting(&cw)
    }

    /// The core Theorem-A check: the circuit accepts exactly when the native
    /// SMT semantics hold, for a valid witness and for a perturbed one (with
    /// the public inputs held fixed from the valid setup).
    fn assert_equivalence(
        params: &SmtParams,
        op: &SmtOperation,
        pi: &PublicInputs,
        valid: &SmtWitness,
        perturbed: &SmtWitness,
    ) {
        let h = Poseidon2Gadget::default();
        let native = |w: &SmtWitness| {
            smt_valid_native(&h, params, op, &pi.old_root, &pi.new_root, w).unwrap()
        };
        assert!(
            circuit_accepts(params, op, pi, valid),
            "circuit should accept valid"
        );
        assert!(native(valid), "native should accept valid");
        assert_eq!(
            circuit_accepts(params, op, pi, perturbed),
            native(perturbed),
            "circuit and native must agree on the perturbed witness"
        );
        assert!(!native(perturbed), "perturbation should break validity");
    }

    #[test]
    fn membership_theorem_a() {
        let h = Poseidon2Gadget::default();
        let params = SmtParams {
            depth: 4,
            ..Default::default()
        };
        let key = AssetId(5);
        let payload = LeafPayload {
            sync_state: vec![f(42), f(43)],
            identity_digest: [7u8; 32],
        };
        let leaf = LeafState::Occupied(payload.clone());
        let path = MerklePath {
            siblings: siblings(4),
        };
        let old_root = path.compute_root(&h, &params, key, &leaf).unwrap();
        let value_digest = h.hash_leaf(&leaf.encode()).unwrap();
        let op = SmtOperation::Membership { key, payload };
        let pi = PublicInputs {
            old_root,
            new_root: old_root,
            op_kind_tag: 0,
            asset_id: key,
            value_digest,
        };
        let valid = SmtWitness {
            leaf,
            path: path.clone(),
        };
        let mut perturbed = valid.clone();
        perturbed.path.siblings[1] = Digest([f(999); DIGEST_WIDTH]);
        assert_equivalence(&params, &op, &pi, &valid, &perturbed);
    }

    #[test]
    fn non_membership_theorem_a() {
        let h = Poseidon2Gadget::default();
        let params = SmtParams {
            depth: 5,
            ..Default::default()
        };
        let key = AssetId(11);
        let leaf = LeafState::Tombstone;
        let path = MerklePath {
            siblings: siblings(5),
        };
        let old_root = path.compute_root(&h, &params, key, &leaf).unwrap();
        let value_digest = h.hash_leaf(&leaf.encode()).unwrap();
        let op = SmtOperation::NonMembership { key };
        let pi = PublicInputs {
            old_root,
            new_root: old_root,
            op_kind_tag: 1,
            asset_id: key,
            value_digest,
        };
        let valid = SmtWitness { leaf, path };
        // Perturb the leaf: Empty instead of Tombstone changes the leaf hash.
        let mut perturbed = valid.clone();
        perturbed.leaf = LeafState::Empty;
        assert_equivalence(&params, &op, &pi, &valid, &perturbed);
    }

    #[test]
    fn update_theorem_a() {
        let h = Poseidon2Gadget::default();
        let params = SmtParams {
            depth: 4,
            ..Default::default()
        };
        let key = AssetId(9);
        let payload = LeafPayload {
            sync_state: vec![f(100)],
            identity_digest: [3u8; 32],
        };
        let old_leaf = LeafState::Occupied(payload);
        let new_leaf = LeafState::Tombstone;
        let path = MerklePath {
            siblings: siblings(4),
        };
        let old_root = path.compute_root(&h, &params, key, &old_leaf).unwrap();
        let new_root = path.compute_root(&h, &params, key, &new_leaf).unwrap();
        let value_digest = h.hash_leaf(&new_leaf.encode()).unwrap();
        let op = SmtOperation::Update {
            key,
            old_leaf: old_leaf.clone(),
            new_leaf,
        };
        let pi = PublicInputs {
            old_root,
            new_root,
            op_kind_tag: 2,
            asset_id: key,
            value_digest,
        };
        let valid = SmtWitness {
            leaf: old_leaf,
            path: path.clone(),
        };
        let mut perturbed = valid.clone();
        perturbed.path.siblings[2] = Digest([f(777); DIGEST_WIDTH]);
        assert_equivalence(&params, &op, &pi, &valid, &perturbed);
    }

    #[test]
    fn unsupported_strategy_is_rejected() {
        let params = SmtParams {
            depth: 4,
            ..Default::default()
        };
        let template = Poseidon2Gadget::default().round_template();
        assert!(matches!(
            compile(&params, SmtOpKind::Membership, LayerStrategy::C, &template),
            Err(CompileError::UnsupportedConfig { .. })
        ));
    }

    // ---------------------------------------------------------------------
    // Poseidon2 arithmetization cross-checks: the emitted circuit gadgets must
    // reproduce the native Poseidon2 gadget EXACTLY. These are the correctness
    // pins for the in-circuit arithmetization (N2): the permutation block, the
    // node compression, and the leaf sponge across all leaf states/lengths.

    fn rand_state(seed: u32) -> [BaseField; P2W] {
        core::array::from_fn(|i| {
            f(seed
                .wrapping_mul(2_654_435_761)
                .wrapping_add(i as u32 * 40_503 + 7)
                % 1_000_003)
        })
    }

    /// The emitted permutation block equals the native
    /// `default_koalabear_poseidon2_16().permute()` on random states.
    #[test]
    fn poseidon2_permutation_matches_native() {
        let mut b = Builder::new(P2W as u32);
        let inputs: [NodeId; P2W] = core::array::from_fn(|i| b.input(i as u32));
        let out = emit_permutation(&mut b, &inputs);
        let circuit = b.build(&out);
        validate_unary_gates(&circuit).expect("permutation gates are S-3 unary");
        for seed in 0..8 {
            let state = rand_state(seed);
            let cw = evaluate_circuit(&circuit, &state).unwrap();
            let native = p2::permute(state);
            for (z, &nv) in native.iter().enumerate() {
                assert_eq!(cw.layer_values[0][z], nv, "perm lane {z} seed {seed}");
            }
        }
    }

    /// The emitted node hash equals `Poseidon2Gadget::compress` (truncated perm).
    #[test]
    fn poseidon2_compress_matches_native() {
        let h = Poseidon2Gadget::default();
        let mut b = Builder::new(P2W as u32);
        let left: Vec<NodeId> = (0..W).map(|i| b.input(i)).collect();
        let right: Vec<NodeId> = (W..2 * W).map(|i| b.input(i)).collect();
        let out = build_node_hash(&mut b, &left, &right);
        let circuit = b.build(&out);
        validate_unary_gates(&circuit).expect("node hash gates are S-3 unary");
        for seed in 0..8 {
            let st = rand_state(seed);
            let l: [BaseField; DIGEST_WIDTH] = core::array::from_fn(|i| st[i]);
            let r: [BaseField; DIGEST_WIDTH] = core::array::from_fn(|i| st[DIGEST_WIDTH + i]);
            let cw = evaluate_circuit(&circuit, &st).unwrap();
            let native = h.compress(&Digest(l), &Digest(r)).0;
            for (i, &nv) in native.iter().enumerate() {
                assert_eq!(cw.layer_values[0][i], nv, "compress lane {i} seed {seed}");
            }
        }
    }

    /// The emitted leaf hash equals `Poseidon2Gadget::hash_leaf` for all three
    /// leaf states across an in-bound encoding-length sweep (short, the old
    /// 16-lane boundary, beyond it, and the exact `leaf_max_fields` bound).
    /// The R2-1 tag lane (`leaf_pre[0] == tag`) and the CR length lane
    /// (`leaf_pre[1] == encoding length`) are pinned alongside so the
    /// guarantees stay coupled.
    #[test]
    fn poseidon2_leaf_hash_matches_native() {
        let max = DEFAULT_LEAF_MAX_FIELDS;
        let lanes = leaf_pre_width(max) as u32;
        let h = Poseidon2Gadget::default();
        let mut b = Builder::new(lanes);
        let pre: Vec<NodeId> = (0..lanes).map(|i| b.input(i)).collect();
        let out = build_leaf_hash(&mut b, &pre);
        let circuit = b.build(&out);
        validate_unary_gates(&circuit).expect("leaf hash gates are S-3 unary");

        let occ = |n: usize, tag: u8| {
            LeafState::Occupied(LeafPayload {
                sync_state: (0..n).map(|i| f(i as u32 + 1)).collect(),
                identity_digest: [tag; 32],
            })
        };
        // (leaf, expected tag). Encoding length = 1 + sync_state.len() + 9.
        let cases = [
            (LeafState::Empty, 0u32),
            (LeafState::Tombstone, 2),
            (occ(1, 3), 1),  // encoding 11 (short)
            (occ(6, 5), 1),  // encoding 16 (the old fold's lane boundary)
            (occ(7, 7), 1),  // encoding 17 (beyond it - pre-fix wrap zone)
            (occ(21, 9), 1), // encoding 31 (= the exact leaf_max_fields bound)
        ];
        for (leaf, tag) in cases {
            let enc = leaf.encode();
            let fold = leaf_fold(&enc, max).unwrap();
            assert_eq!(
                fold[0],
                f(tag),
                "R2-1: leaf_pre[0] == tag (len {})",
                enc.len()
            );
            assert_eq!(
                fold[1],
                f(enc.len() as u32),
                "CR fix: leaf_pre[1] == encoding length"
            );
            let cw = evaluate_circuit(&circuit, &fold).unwrap();
            let native = h.hash_leaf(&enc).unwrap().0;
            for (i, &nv) in native.iter().enumerate() {
                assert_eq!(
                    cw.layer_values[0][i],
                    nv,
                    "leaf lane {i} tag {tag} len {}",
                    enc.len()
                );
            }
        }
    }

    /// The structural bound: an encoding longer than `leaf_max_fields` is a
    /// hash-time error (never hashed lossily), witness generation refuses it,
    /// and `compile` rejects a bound too small to admit any Occupied leaf.
    #[test]
    fn leaf_encoding_bound_is_structural() {
        let h = Poseidon2Gadget::default();
        // sync_state 22 -> encoding 32 > 31 (the default bound).
        let over = LeafState::Occupied(LeafPayload {
            sync_state: (0..22).map(|i| f(i + 1)).collect(),
            identity_digest: [1u8; 32],
        });
        assert!(h.hash_leaf(&over.encode()).is_err(), "oversized -> Err");
        assert!(leaf_fold(&over.encode(), DEFAULT_LEAF_MAX_FIELDS).is_err());

        // compute_root (native semantics) surfaces the same structural error.
        let params = SmtParams {
            depth: 4,
            ..Default::default()
        };
        let path = MerklePath {
            siblings: siblings(4),
        };
        assert!(
            path.compute_root(&h, &params, AssetId(5), &over).is_err(),
            "native path computation refuses an out-of-bound leaf"
        );

        // A bound too small for any Occupied leaf is a config error.
        let bad = SmtParams {
            depth: 4,
            leaf_max_fields: 9,
        };
        let template = Poseidon2Gadget::default().round_template();
        assert!(matches!(
            compile(&bad, SmtOpKind::Membership, LayerStrategy::A, &template),
            Err(CompileError::UnsupportedConfig { .. })
        ));
    }
}
