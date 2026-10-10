//! Layered arithmetic circuit IR and its native semantics.
//!
//! SEAL[S-3] (amended at the design-freeze gate): the IR shape (layer
//! list, gate family {Lin, Mul, Pow3} with per-gate coefficients, plus a
//! per-layer additive constant vector) and [`gate_semantics`] are frozen
//! together with the Isabelle definitions `gate_kind` / `gate_sem` /
//! `layer_eval` in `formal/isabelle/GKR_Protocol/Layered_Circuit.thy`.
//! The two MUST stay
//! literally in sync; any gate-family change is a design-review event
//! (it changes the wiring-predicate family and thus the Theorem B
//! statement).
//!
//! Why this algebra (freeze-gate counterexample record): the dominant
//! workload is Poseidon2, whose rounds are `x^3` S-boxes composed with
//! AFFINE layers (MDS constant multiplications + round-constant
//! additions). A plain {Add, Mul, Pow3} set cannot express constant
//! scaling or constant addition, so it would have broken in the first
//! week of implementation. The frozen layer identity is therefore:
//!
//! ```text
//! V_i(z) = const_i(z)
//!        + sum over Lin  gates (out=z):  coeff * V_{i+1}(in1)
//!        + sum over Mul  gates (out=z):  coeff * V_{i+1}(in1) * V_{i+1}(in2)
//!        + sum over Pow3 gates (out=z):  coeff * V_{i+1}(in1)^3
//! ```
//!
//! which keeps per-layer degree <= 3 and expresses affine layers
//! natively (`Add` is just two `Lin` gates accumulating into one output,
//! so the family is smaller AND more expressive than {Add, Mul, Pow3}).
//! In MLE form the per-kind wiring predicates become F-VALUED sparse
//! functions (coefficients embedded in the predicate value) plus one
//! multilinear constant term - the standard Libra-style generalization.

use ssgkr_primitives::field::Field;

#[cfg(creusot)]
use creusot_std::prelude::{ensures, requires, trusted};

/// Gate kinds of the v0.1 circuit IR.
///
/// Isabelle: `datatype gate_kind = GLin | GMul | GPow3`.
///
/// `Lin` and `Pow3` are UNARY: `in2` is ignored and by convention MUST
/// be set equal to `in1` (the compiler validates this invariant when
/// laying out circuits).
///
/// Fieldless enum, so the Creusot build derives a `DeepModel` (class-2
/// container, R1 boundary rule) and `PartialEq` stays available to the
/// production bodies that branch on gate kinds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(creusot, derive(creusot_std::prelude::DeepModel))]
pub enum GateKind {
    /// `out += coeff * a` (weighted wire copy; affine layers, MDS rows).
    Lin,
    /// `out += coeff * a * b`.
    Mul,
    /// `out += coeff * a^3` (Poseidon2 S-box; unary).
    Pow3,
}

/// Native gate semantics (kind part only - the coefficient is applied by
/// the LAYER evaluation, mirroring the Isabelle split where `gate_sem`
/// is coefficient-free and `layer_eval` multiplies the wiring weight).
///
/// Isabelle: `gate_sem` - keep literally in sync (this function is the
/// semantic anchor the compiled circuits are verified against).
///
/// R2 contract: the `Lin` clause (`gate_sem GLin a b = a`) is
/// machine-checked - the arm returns its argument, a pure structural
/// fact. The `Mul`/`Pow3` clauses (`a * b`, `a * a * a`) are
/// EXPRESSION-WALLED: the products dispatch through the contract-free
/// plonky3 operator impls (design B.6 black box), so there is no
/// logic-level `*` to state them against. Held by the model
/// (`Layered_Circuit.gate_sem_simps`).
#[cfg_attr(creusot, ensures(kind == GateKind::Lin ==> result == a))]
pub fn gate_semantics<F: Field>(kind: GateKind, a: F, b: F) -> F {
    match kind {
        GateKind::Lin => a,
        GateKind::Mul => a * b,
        GateKind::Pow3 => a * a * a,
    }
}

/// One weighted gate: `(kind, out, in1, in2, coeff)` with wire indices
/// into the layer below. For unary kinds (`Lin`, `Pow3`) set
/// `in2 == in1`.
///
/// `PartialEq`/`Eq` gated out of the Creusot build (generic `F` cannot
/// carry `DeepModel`; see `ssgkr_sumcheck::MultilinearPoly`).
#[derive(Clone, Copy, Debug)]
#[cfg_attr(not(creusot), derive(PartialEq, Eq))]
pub struct Gate<F> {
    /// Gate kind.
    pub kind: GateKind,
    /// Output wire index in this layer.
    pub out: u32,
    /// First input wire index in the layer below.
    pub in1: u32,
    /// Second input wire index in the layer below (== `in1` for unary
    /// kinds by convention).
    pub in2: u32,
    /// Multiplicative coefficient applied to the gate's contribution.
    pub coeff: F,
}

/// One circuit layer. `width_bits` is log2 of the wire count (GKR works
/// over hypercube-indexed wires).
///
/// `PartialEq`/`Eq` gated out of the Creusot build (generic `F`).
#[derive(Clone, Debug)]
#[cfg_attr(not(creusot), derive(PartialEq, Eq))]
pub struct Layer<F> {
    /// log2(number of wires in this layer).
    pub width_bits: usize,
    /// Weighted gates producing this layer from the layer below.
    pub gates: Vec<Gate<F>>,
    /// Sparse additive constants `(wire, value)` (round constants etc.);
    /// wires not listed default to zero. Isabelle: `consts` function.
    pub consts: Vec<(u32, F)>,
}

impl<F> Layer<F> {
    /// Number of wires (2^width_bits).
    ///
    /// The `requires` is the machine-width side condition of the shift
    /// (the model's `layer_width` is over unbounded nat). Stated in
    /// shift notation - the int-mode prelude declares the bitwise ops
    /// without axioms (R1 wall 3), so `2^n` arithmetic is out of
    /// machine reach; syntactic mirroring is the proving path (the R1
    /// `path_root` precedent).
    #[cfg_attr(creusot, requires(self.width_bits@ < 64))]
    pub fn width(&self) -> usize {
        1 << self.width_bits
    }
}

/// Layered circuit: `layers[0]` is the OUTPUT layer, the last entry reads
/// from the input vector (same orientation as the Isabelle sketch).
///
/// `PartialEq`/`Eq` gated out of the Creusot build (generic `F`).
#[derive(Clone, Debug)]
#[cfg_attr(not(creusot), derive(PartialEq, Eq))]
pub struct LayeredCircuit<F> {
    /// Output layer first, deepest (input-adjacent) layer last.
    pub layers: Vec<Layer<F>>,
    /// log2(number of input wires).
    pub input_width_bits: usize,
}

impl<F> LayeredCircuit<F> {
    /// Total number of layers (excluding the input vector).
    #[cfg_attr(creusot, ensures(result@ == self.layers@.len()))]
    pub fn depth(&self) -> usize {
        self.layers.len()
    }
}

/// All wire values of one execution, layer by layer.
///
/// `layer_values[0]` = output layer values, then inward; the input vector
/// is stored last. Produced by [`evaluate_circuit`]; consumed by the GKR
/// prover as the witness.
///
/// `PartialEq`/`Eq` gated out of the Creusot build (generic `F`).
#[derive(Clone, Debug)]
#[cfg_attr(not(creusot), derive(PartialEq, Eq))]
pub struct CircuitWitness<F> {
    /// Values per layer, output layer first, inputs last.
    pub layer_values: Vec<Vec<F>>,
}

/// Errors from circuit evaluation.
///
/// `PartialEq`/`Eq` gated out of the Creusot build (no contract consumes
/// error equality; see `ssgkr_sumcheck::SumcheckError`).
#[derive(Clone, Debug)]
#[cfg_attr(not(creusot), derive(PartialEq, Eq))]
pub enum CircuitError {
    /// Input vector length does not match `input_width_bits`.
    InputWidthMismatch {
        /// Expected length (2^input_width_bits).
        expected: usize,
        /// Provided length.
        found: usize,
    },
    /// A gate or constant references a wire index out of range.
    WireOutOfRange {
        /// Layer index (0 = output layer).
        layer: usize,
    },
}

/// Native circuit semantics: compute every layer from the inputs.
///
/// Isabelle: `circuit_eval` (foldr over `layer_eval`) - spec-literal,
/// serves as the test oracle for both the compiler (Theorem A tests) and
/// the GKR prover witness generation. 2a may add a fast path but this
/// definition stays the reference.
///
/// FV-CONTRACT (Creusot, R1/R2 shared anchor - design contract, NOT
/// tool-checked):
///   #[requires(inputs.len() == 1 << circuit.input_width_bits)]
///   #[ensures(Ok(w) ==> w.layer_values.len() == circuit.layers.len() + 1)]
///   #[ensures(Ok(w) ==> each layer vector equals Layered_Circuit.layer_eval
///       of the one below it (circuit_values, output layer first))]
/// TOOL WALL (R2 dev, honest carry-over; `#[trusted]` = translation
/// opt-out carrying ZERO claims): the body iterates
/// `layers.iter().enumerate().rev()`, and creusot-std has no
/// `DoubleEndedIteratorSpec` instance for `Enumerate` - a hard
/// translation error (E0277), same missing-iterator-spec class as the
/// R1 `Iterator::unzip` wall (wall 1). The value clause is additionally
/// expression-walled (black-box field ops). Held by the model side
/// (`circuit_values`, `layer_eval`).
#[cfg_attr(creusot, trusted)]
pub fn evaluate_circuit<F: Field>(
    circuit: &LayeredCircuit<F>,
    inputs: &[F],
) -> Result<CircuitWitness<F>, CircuitError> {
    let expected = 1usize << circuit.input_width_bits;
    if inputs.len() != expected {
        return Err(CircuitError::InputWidthMismatch {
            expected,
            found: inputs.len(),
        });
    }

    // Evaluate inward-out: start from inputs, apply layers from deepest
    // (last) to output (first).
    let mut below: Vec<F> = inputs.to_vec();
    let mut acc: Vec<Vec<F>> = Vec::with_capacity(circuit.layers.len() + 1);
    acc.push(below.clone()); // input vector, will end up LAST after reverse

    for (idx, layer) in circuit.layers.iter().enumerate().rev() {
        let mut values = vec![F::ZERO; layer.width()];
        for &(wire, c) in &layer.consts {
            let wire = wire as usize;
            if wire >= values.len() {
                return Err(CircuitError::WireOutOfRange { layer: idx });
            }
            values[wire] += c;
        }
        for gate in &layer.gates {
            let a = *below
                .get(gate.in1 as usize)
                .ok_or(CircuitError::WireOutOfRange { layer: idx })?;
            let b = *below
                .get(gate.in2 as usize)
                .ok_or(CircuitError::WireOutOfRange { layer: idx })?;
            let out = gate.out as usize;
            if out >= values.len() {
                return Err(CircuitError::WireOutOfRange { layer: idx });
            }
            values[out] += gate.coeff * gate_semantics(gate.kind, a, b);
        }
        below = values.clone();
        acc.push(values);
    }

    acc.reverse(); // output layer first, inputs last
    Ok(CircuitWitness { layer_values: acc })
}
