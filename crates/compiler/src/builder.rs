//! A small auto-layering circuit builder.
//!
//! Hand-laying a layered circuit (assigning wires, aligning depths, carrying
//! values through intermediate layers) is where the soundness-critical
//! Module-1 bugs would hide. Instead the compiler describes the computation
//! as a DAG of typed nodes and this builder lays it out into the
//! [`LayeredCircuit`] IR: it computes each node's level, inserts identity
//! copy nodes to bridge multi-level edges, groups nodes into layers and
//! emits gates. Identical sub-DAGs (one per tree level) produce identical
//! layers, which is exactly the data-parallel regular structure strategy A
//! relies on.
//!
//! Every emitted `Lin`/`Pow3` gate is unary with `in2 == in1` (S-3
//! convention); `Mul` is the only binary kind.
//!
//! # Family scopes (the succinct-verifier layout contract)
//!
//! The compiler wraps each data-parallel construction site in a
//! [`Builder::scope`] `(family, block)`; nodes (and the copies later
//! inserted for them) carry that tag. At layout time every level places
//! each family in its own WINDOW, blocks at a power-of-two stride from a
//! stride-aligned base - exactly the aligned arithmetic progressions
//! `DerivedRegularWiring::derive` factors into the closed-form (succinct)
//! wiring oracle. Tags are hints only: the derivation re-verifies every
//! progression and drops misfits to an exact sparse path, so scoping
//! mistakes cost verifier speed, never soundness.

use std::collections::{BTreeMap, HashMap};

use ssgkr_primitives::field::{BaseField, Field, PrimeCharacteristicRing};
use ssgkr_protocol::{FamilyTag, Gate, GateKind, Layer, LayerHints, LayeredCircuit, WiringHints};

// Under `--cfg creusot` the verifier's `PartialEq` derive needs a
// `DeepModel` on the type. `TapKind` is simply derived; `NodeId` keeps its
// field private (opaque handle), which the derive's transparent logic
// function cannot expose, so its model is spelled out (non-transparent).
#[cfg(creusot)]
use creusot_std::prelude::{DeepModel, Int, logic, pearlite};

/// Handle to a node in the builder DAG.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NodeId(usize);

#[cfg(creusot)]
impl DeepModel for NodeId {
    type DeepModelTy = Int;

    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { self.0@ }
    }
}

/// Per-tap S-3 gate kind inside a fused [`Builder::combine`] node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(creusot, derive(DeepModel))]
pub enum TapKind {
    /// `coeff * child` (emits a `Lin` gate).
    Lin,
    /// `coeff * child^3` (emits a `Pow3` gate).
    Cube,
}

enum Op {
    /// A wire of the input vector at the given index.
    Input(u32),
    /// `sum_k coeff_k * child_k + cst` (affine combination; empty = const).
    Affine {
        terms: Vec<(NodeId, BaseField)>,
        cst: BaseField,
    },
    /// `a * b` (the only binary gate).
    Mul(NodeId, NodeId),
    /// `a^3`.
    Pow3(NodeId),
    /// Fused affine+cube combination into one output wire:
    /// `sum_k coeff_k * f_k(child_k) + cst`, where `f_k` is identity
    /// (`TapKind::Lin`) or cube (`TapKind::Cube`). Emits one S-3 gate per tap
    /// into the SAME output wire (they accumulate) plus the additive constant.
    /// This is one Poseidon2 round as a single GKR layer.
    Combine {
        terms: Vec<(NodeId, BaseField, TapKind)>,
        cst: BaseField,
    },
}

/// Auto-layering DAG circuit builder.
pub struct Builder {
    ops: Vec<Op>,
    level: Vec<usize>,
    tags: Vec<Option<FamilyTag>>,
    scope: Option<FamilyTag>,
    input_width: u32,
    copies: HashMap<(NodeId, usize), NodeId>,
}

/// `ceil(log2(max(n, 1)))` - the `width_bits` holding `n` wires.
pub fn width_bits(n: usize) -> usize {
    n.max(1).next_power_of_two().trailing_zeros() as usize
}

impl Builder {
    /// New builder over an input vector of `input_width` wires.
    pub fn new(input_width: u32) -> Self {
        Self {
            ops: Vec::new(),
            level: Vec::new(),
            tags: Vec::new(),
            scope: None,
            input_width,
            copies: HashMap::new(),
        }
    }

    /// Open a family scope: nodes created until [`Self::unscope`] are tagged
    /// `(family, block)`. Blocks of one family must be built by the SAME
    /// code path so their per-level node sequences match slot-for-slot.
    pub fn scope(&mut self, family: u32, block: u32) {
        self.scope = Some(FamilyTag { family, block });
    }

    /// Close the current family scope (subsequent nodes are untagged glue).
    pub fn unscope(&mut self) {
        self.scope = None;
    }

    fn push(&mut self, op: Op, level: usize) -> NodeId {
        let tag = self.scope;
        self.push_tagged(op, level, tag)
    }

    fn push_tagged(&mut self, op: Op, level: usize, tag: Option<FamilyTag>) -> NodeId {
        let id = NodeId(self.ops.len());
        self.ops.push(op);
        self.level.push(level);
        self.tags.push(tag);
        id
    }

    /// Reference input wire `idx` (level 0).
    pub fn input(&mut self, idx: u32) -> NodeId {
        debug_assert!(idx < self.input_width, "input index out of range");
        self.push(Op::Input(idx), 0)
    }

    /// A constant wire.
    pub fn constant(&mut self, c: BaseField) -> NodeId {
        self.push(
            Op::Affine {
                terms: vec![],
                cst: c,
            },
            1,
        )
    }

    /// Affine combination `sum coeff*child + cst`.
    pub fn affine(&mut self, terms: Vec<(NodeId, BaseField)>, cst: BaseField) -> NodeId {
        let level = 1 + terms
            .iter()
            .map(|&(n, _)| self.level[n.0])
            .max()
            .unwrap_or(0);
        self.push(Op::Affine { terms, cst }, level)
    }

    /// Sum of wires (unit coefficients).
    pub fn sum(&mut self, children: &[NodeId]) -> NodeId {
        self.affine(
            children.iter().map(|&c| (c, BaseField::ONE)).collect(),
            BaseField::ZERO,
        )
    }

    /// `a - b`.
    pub fn sub(&mut self, a: NodeId, b: NodeId) -> NodeId {
        self.affine(
            vec![(a, BaseField::ONE), (b, -BaseField::ONE)],
            BaseField::ZERO,
        )
    }

    /// `a * b`.
    pub fn mul(&mut self, a: NodeId, b: NodeId) -> NodeId {
        let level = 1 + self.level[a.0].max(self.level[b.0]);
        self.push(Op::Mul(a, b), level)
    }

    /// `a^3`.
    pub fn pow3(&mut self, a: NodeId) -> NodeId {
        let level = 1 + self.level[a.0];
        self.push(Op::Pow3(a), level)
    }

    /// A fused round layer: `sum_k coeff_k * f_k(child_k) + cst` accumulated
    /// into one output wire, where each tap's `f_k` is identity ([`TapKind::Lin`])
    /// or cube ([`TapKind::Cube`]). This is one Poseidon2 round written as a
    /// single GKR layer (the S-box cube and the matrix multiply fused; the
    /// round constant of the NEXT cube rides in `cst`). Every emitted gate
    /// stays within the frozen S-3 family (`Lin`/`Pow3`, unary `in2 == in1`).
    pub fn combine(&mut self, terms: Vec<(NodeId, BaseField, TapKind)>, cst: BaseField) -> NodeId {
        let level = 1 + terms
            .iter()
            .map(|&(n, _, _)| self.level[n.0])
            .max()
            .unwrap_or(0);
        self.push(Op::Combine { terms, cst }, level)
    }

    /// Lift `node` to `target` level via a chain of identity copies. Copies
    /// inherit the SOURCE node's family tag (a carried value stays in its
    /// family's window at every level it crosses).
    fn lift(&mut self, node: NodeId, target: usize) -> NodeId {
        let mut cur = node;
        while self.level[cur.0] < target {
            let next_level = self.level[cur.0] + 1;
            cur = if let Some(&c) = self.copies.get(&(cur, next_level)) {
                c
            } else {
                let tag = self.tags[cur.0];
                let copy = self.push_tagged(
                    Op::Affine {
                        terms: vec![(cur, BaseField::ONE)],
                        cst: BaseField::ZERO,
                    },
                    next_level,
                    tag,
                );
                self.copies.insert((cur, next_level), copy);
                copy
            };
        }
        cur
    }

    /// Lay out the DAG into a circuit whose OUTPUT layer is exactly the
    /// `outputs` wires (in the given order), all lifted to a common top
    /// level. The acceptance convention (all output wires zero) is applied
    /// by the caller via `is_accepting`.
    pub fn build(self, outputs: &[NodeId]) -> LayeredCircuit<BaseField> {
        self.build_with_hints(outputs).0
    }

    /// [`Self::build`] plus the per-gate/const [`WiringHints`] the derived
    /// closed-form wiring oracle consumes (`DerivedRegularWiring::derive`).
    ///
    /// `trusted` under Creusot: the body iterates `BTreeMap` (no
    /// `IteratorSpec` in creusot-std at the pinned rev) and is outside the
    /// current refinement scope - the R1 anchor for layout correctness is
    /// the compiled circuit's semantics, not the builder's internal wire
    /// placement (which `validate_unary_gates` + the derived-wiring
    /// re-verification check dynamically).
    #[cfg_attr(creusot, creusot_std::prelude::trusted)]
    pub fn build_with_hints(
        mut self,
        outputs: &[NodeId],
    ) -> (LayeredCircuit<BaseField>, WiringHints) {
        let out_level = outputs
            .iter()
            .map(|&o| self.level[o.0])
            .max()
            .unwrap_or(0)
            .max(1);
        let outs: Vec<NodeId> = outputs.iter().map(|&o| self.lift(o, out_level)).collect();

        // Align every gate node's children to exactly (node level - 1).
        let snapshot = self.ops.len();
        for id in 0..snapshot {
            let lvl = self.level[id];
            if lvl == 0 {
                continue;
            }
            let target = lvl - 1;
            let rewritten = match &self.ops[id] {
                Op::Input(_) => None,
                Op::Affine { terms, cst } => {
                    let cst = *cst;
                    let terms: Vec<(NodeId, BaseField)> = terms.clone();
                    let lifted = terms
                        .into_iter()
                        .map(|(n, c)| (self.lift(n, target), c))
                        .collect();
                    Some(Op::Affine { terms: lifted, cst })
                }
                Op::Mul(a, b) => {
                    let (a, b) = (*a, *b);
                    Some(Op::Mul(self.lift(a, target), self.lift(b, target)))
                }
                Op::Pow3(a) => {
                    let a = *a;
                    Some(Op::Pow3(self.lift(a, target)))
                }
                Op::Combine { terms, cst } => {
                    let cst = *cst;
                    let terms: Vec<(NodeId, BaseField, TapKind)> = terms.clone();
                    let lifted = terms
                        .into_iter()
                        .map(|(n, c, k)| (self.lift(n, target), c, k))
                        .collect();
                    Some(Op::Combine { terms: lifted, cst })
                }
            };
            if let Some(op) = rewritten {
                self.ops[id] = op;
            }
        }

        // Assign a wire index to every node within its level. Interior
        // levels place each family in its own window - blocks at a
        // power-of-two stride from a stride-ALIGNED base - which is the
        // layout contract the derived closed-form wiring factors over
        // (alignment holes are legal wires that stay zero). Untagged glue
        // packs after the windows. Level 0 keeps input positions; the
        // output level keeps id order (remapped to output order below).
        let mut wire = vec![0u32; self.ops.len()];
        let mut count_per_level = vec![0u32; out_level + 1];
        let mut per_level: Vec<Vec<usize>> = vec![Vec::new(); out_level + 1];
        for (id, &lvl) in self.level.iter().enumerate() {
            if let Op::Input(idx) = self.ops[id] {
                wire[id] = idx;
            } else {
                per_level[lvl].push(id);
            }
        }
        for (lvl, ids) in per_level.iter().enumerate().skip(1) {
            if lvl == out_level {
                for (k, &id) in ids.iter().enumerate() {
                    wire[id] = k as u32;
                }
                count_per_level[lvl] = ids.len() as u32;
                continue;
            }
            let mut fams: BTreeMap<u32, BTreeMap<u32, Vec<usize>>> = BTreeMap::new();
            let mut misc: Vec<usize> = Vec::new();
            for &id in ids {
                match self.tags[id] {
                    Some(t) => fams
                        .entry(t.family)
                        .or_default()
                        .entry(t.block)
                        .or_default()
                        .push(id),
                    None => misc.push(id),
                }
            }
            let mut cursor: u32 = 0;
            for blocks in fams.into_values() {
                let nblocks = blocks.len() as u32;
                let bsize = blocks.values().map(|v| v.len()).max().unwrap_or(0) as u32;
                let stride = bsize.max(1).next_power_of_two();
                cursor = cursor.div_ceil(stride) * stride;
                for (rank, ids_b) in blocks.values().enumerate() {
                    for (slot, &id) in ids_b.iter().enumerate() {
                        wire[id] = cursor + rank as u32 * stride + slot as u32;
                    }
                }
                cursor += nblocks * stride;
            }
            for &id in &misc {
                wire[id] = cursor;
                cursor += 1;
            }
            count_per_level[lvl] = cursor;
        }

        // Emit one Layer per level, output layer (top) first, with the
        // per-gate/const family tags riding along as WiringHints.
        let mut layers: Vec<Layer<BaseField>> = Vec::with_capacity(out_level);
        let mut hint_layers: Vec<LayerHints> = Vec::with_capacity(out_level);
        for lvl in (1..=out_level).rev() {
            let count = count_per_level[lvl] as usize;
            let mut gates = Vec::new();
            let mut consts = Vec::new();
            let mut gate_tags = Vec::new();
            let mut const_tags = Vec::new();
            for id in 0..self.ops.len() {
                if self.level[id] != lvl {
                    continue;
                }
                let out = wire[id];
                let tag = self.tags[id];
                match &self.ops[id] {
                    Op::Input(_) => {}
                    Op::Affine { terms, cst } => {
                        for &(child, coeff) in terms {
                            let w = wire[child.0];
                            gates.push(Gate {
                                kind: GateKind::Lin,
                                out,
                                in1: w,
                                in2: w,
                                coeff,
                            });
                            gate_tags.push(tag);
                        }
                        if !cst.is_zero() {
                            consts.push((out, *cst));
                            const_tags.push(tag);
                        }
                    }
                    Op::Mul(a, b) => {
                        gates.push(Gate {
                            kind: GateKind::Mul,
                            out,
                            in1: wire[a.0],
                            in2: wire[b.0],
                            coeff: BaseField::ONE,
                        });
                        gate_tags.push(tag);
                    }
                    Op::Pow3(a) => {
                        let w = wire[a.0];
                        gates.push(Gate {
                            kind: GateKind::Pow3,
                            out,
                            in1: w,
                            in2: w,
                            coeff: BaseField::ONE,
                        });
                        gate_tags.push(tag);
                    }
                    Op::Combine { terms, cst } => {
                        for &(child, coeff, kind) in terms {
                            let w = wire[child.0];
                            let gkind = match kind {
                                TapKind::Lin => GateKind::Lin,
                                TapKind::Cube => GateKind::Pow3,
                            };
                            gates.push(Gate {
                                kind: gkind,
                                out,
                                in1: w,
                                in2: w,
                                coeff,
                            });
                            gate_tags.push(tag);
                        }
                        if !cst.is_zero() {
                            consts.push((out, *cst));
                            const_tags.push(tag);
                        }
                    }
                }
            }
            layers.push(Layer {
                width_bits: width_bits(count.max(1)),
                gates,
                consts,
            });
            hint_layers.push(LayerHints {
                gates: gate_tags,
                consts: const_tags,
            });
        }

        // Reorder the output layer's wires to match `outs` order 0..n
        // (build already placed them at the top level; rewire by remapping).
        // Since outputs are the ONLY nodes at out_level, their wire indices
        // are a permutation of 0..num_outputs; remap so output k -> wire k.
        let output_layer = &mut layers[0];
        let mut remap: HashMap<u32, u32> = HashMap::new();
        for (k, &o) in outs.iter().enumerate() {
            remap.insert(wire[o.0], k as u32);
        }
        for g in &mut output_layer.gates {
            if let Some(&nw) = remap.get(&g.out) {
                g.out = nw;
            }
        }
        for c in &mut output_layer.consts {
            if let Some(&nw) = remap.get(&c.0) {
                c.0 = nw;
            }
        }

        (
            LayeredCircuit {
                layers,
                input_width_bits: width_bits(self.input_width as usize),
            },
            WiringHints {
                layers: hint_layers,
            },
        )
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;
    use ssgkr_protocol::evaluate_circuit;

    fn f(x: u32) -> BaseField {
        BaseField::from_u32(x)
    }

    #[test]
    fn builds_multi_depth_dag_with_carry() {
        // out0 = (in0 + in1)^3 - in2   (depth 2: affine, cube-sub)
        // out1 = in0 * in3             (depth 1) -> must be lifted to depth 2
        // inputs: [in0, in1, in2, in3]
        let mut b = Builder::new(4);
        let in0 = b.input(0);
        let in1 = b.input(1);
        let in2 = b.input(2);
        let in3 = b.input(3);
        let s = b.sum(&[in0, in1]);
        let cube = b.pow3(s);
        let out0 = b.sub(cube, in2);
        let out1 = b.mul(in0, in3);
        let circuit = b.build(&[out0, out1]);

        let inputs = [f(2), f(3), f(4), f(5)];
        let w = evaluate_circuit(&circuit, &inputs).unwrap();
        // out0 = (2+3)^3 - 4 = 125 - 4 = 121; out1 = 2*5 = 10.
        assert_eq!(w.layer_values[0][0], f(121));
        assert_eq!(w.layer_values[0][1], f(10));
    }

    #[test]
    fn combine_fuses_lin_and_cube_taps_in_one_layer() {
        // out = 2*in0^3 + 3*in1 + 5, all in a single fused layer (one
        // Poseidon2-round shape: mixed Pow3/Lin taps + a constant).
        let mut b = Builder::new(2);
        let in0 = b.input(0);
        let in1 = b.input(1);
        let out = b.combine(
            vec![(in0, f(2), TapKind::Cube), (in1, f(3), TapKind::Lin)],
            f(5),
        );
        let circuit = b.build(&[out]);
        // Exactly one gate layer (the fused combine), reading inputs directly.
        assert_eq!(circuit.layers.len(), 1);
        let w = evaluate_circuit(&circuit, &[f(2), f(4)]).unwrap();
        // 2 * 2^3 + 3 * 4 + 5 = 16 + 12 + 5 = 33.
        assert_eq!(w.layer_values[0][0], f(33));
    }
}
