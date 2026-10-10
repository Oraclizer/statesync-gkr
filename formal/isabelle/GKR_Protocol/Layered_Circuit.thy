(*
  Title:   Layered_Circuit.thy
  Session: GKR_Protocol (generic layer - no SMT / workload assumptions)

  Layered arithmetic circuit IR and its native semantics.

  This theory is the mechanized counterpart of the frozen circuit IR
  (seal point S-3, design-freeze gate): the weighted gate family
  {Lin, Mul, Pow3} (each gate carries a coefficient), plus a per-layer
  additive constant vector.  The layer identity is

    V_i(z) = const_i(z)
           + sum over Lin  gates with out = z:  coeff * V_{i+1}(in1)
           + sum over Mul  gates with out = z:  coeff * V_{i+1}(in1) * V_{i+1}(in2)
           + sum over Pow3 gates with out = z:  coeff * V_{i+1}(in1)^3

  which keeps the per-layer algebraic degree <= 3.

  Rust refinement map (crate `ssgkr-protocol`):
    gate_kind      ~ GateKind::{Lin, Mul, Pow3}
    gate           ~ Gate { kind, out, in1, in2, coeff }
    layer          ~ Layer { width_bits, gates, consts }
    layered_circuit~ LayeredCircuit { layers, input_width_bits }
    gate_sem       ~ gate_semantics       (MUST stay literally in sync)
    layer_eval     ~ the per-layer loop of evaluate_circuit
    circuit_values ~ evaluate_circuit (CircuitWitness, output layer first)
    circuit_accept ~ the facade's output-layer all-zero acceptance (S-4)

  Modeling note: gates form a LIST, not a set.
  The Rust evaluator accumulates contributions with `+=`, so a duplicated
  gate tuple contributes twice; a set-based model would silently collapse
  duplicates and diverge from the implementation.
*)

theory Layered_Circuit
  imports Main
begin

section \<open>Gate kinds and their coefficient-free semantics\<close>

datatype gate_kind = GLin | GMul | GPow3

text \<open>
  Coefficient-free kind semantics; the wiring weight is applied by the
  layer evaluation below (mirroring the Rust split where @{text
  gate_semantics} is coefficient-free and the evaluator multiplies the
  gate coefficient).  \<open>GLin\<close> and \<open>GPow3\<close> are unary: they ignore the
  second argument, and well-formed circuits fix \<open>in2 = in1\<close> by the
  frozen convention.
\<close>

definition gate_sem :: "gate_kind \<Rightarrow> 'f::comm_ring_1 \<Rightarrow> 'f \<Rightarrow> 'f" where
  "gate_sem k a b = (case k of GLin \<Rightarrow> a | GMul \<Rightarrow> a * b | GPow3 \<Rightarrow> a * a * a)"

lemma gate_sem_simps [simp]:
  "gate_sem GLin a b = a"
  "gate_sem GMul a b = a * b"
  "gate_sem GPow3 a b = a * a * a"
  by (simp_all add: gate_sem_def)

section \<open>Gates, layers, circuits\<close>

record 'f gate =
  g_kind  :: gate_kind
  g_out   :: nat
  g_in1   :: nat
  g_in2   :: nat
  g_coeff :: 'f

record 'f layer =
  layer_width_bits :: nat
  layer_gates      :: "'f gate list"
  layer_consts     :: "(nat \<times> 'f) list"

record 'f layered_circuit =
  circ_layers      :: "'f layer list"   \<comment> \<open>output layer first, input-adjacent last\<close>
  input_width_bits :: nat

definition layer_width :: "'f layer \<Rightarrow> nat" where
  "layer_width L = 2 ^ layer_width_bits L"

section \<open>Well-formedness\<close>

text \<open>
  \<open>wf_layer bw L\<close>: every gate writes inside the layer and reads inside the
  layer below (width \<open>bw\<close>), unary kinds satisfy the \<open>in2 = in1\<close> convention
  (Rust: \<open>validate_unary_gates\<close>), and constants target in-range wires.
\<close>

definition wf_gate :: "nat \<Rightarrow> nat \<Rightarrow> 'f gate \<Rightarrow> bool" where
  "wf_gate w bw g \<longleftrightarrow>
     g_out g < w \<and> g_in1 g < bw \<and> g_in2 g < bw \<and>
     (g_kind g = GLin \<or> g_kind g = GPow3 \<longrightarrow> g_in2 g = g_in1 g)"

definition wf_layer :: "nat \<Rightarrow> 'f layer \<Rightarrow> bool" where
  "wf_layer bw L \<longleftrightarrow>
     (\<forall>g \<in> set (layer_gates L). wf_gate (layer_width L) bw g) \<and>
     (\<forall>(w, c) \<in> set (layer_consts L). w < layer_width L)"

text \<open>
  Chain well-formedness: layer \<open>i\<close> reads from layer \<open>i+1\<close>'s width, and the
  deepest layer reads from the input vector.
\<close>

fun wf_chain :: "'f layer list \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_chain [] iw \<longleftrightarrow> True"
| "wf_chain [L] iw \<longleftrightarrow> wf_layer (2 ^ iw) L"
| "wf_chain (L # L' # Ls) iw \<longleftrightarrow> wf_layer (layer_width L') L \<and> wf_chain (L' # Ls) iw"

definition wf_circuit :: "'f layered_circuit \<Rightarrow> bool" where
  "wf_circuit C \<longleftrightarrow> wf_chain (circ_layers C) (input_width_bits C)"

section \<open>Native semantics\<close>

text \<open>
  Additive constant of output wire \<open>z\<close>: sparse (wire, value) list, entries
  for the same wire accumulate (list semantics, mirroring the Rust \<open>+=\<close>
  initialisation loop).
\<close>

definition const_at :: "'f::comm_monoid_add layer \<Rightarrow> nat \<Rightarrow> 'f" where
  "const_at L z = sum_list (map snd (filter (\<lambda>(w, c). w = z) (layer_consts L)))"

text \<open>Contribution of one gate to its output wire, given the layer below.\<close>

definition gate_contrib :: "'f::comm_ring_1 gate \<Rightarrow> 'f list \<Rightarrow> 'f" where
  "gate_contrib g below = g_coeff g * gate_sem (g_kind g) (below ! g_in1 g) (below ! g_in2 g)"

text \<open>
  One layer's value vector from the layer below.  For each output wire:
  the accumulated constant plus the sum of contributions of the gates
  writing to it (list sum - duplicates accumulate).
\<close>

definition layer_eval :: "'f::comm_ring_1 layer \<Rightarrow> 'f list \<Rightarrow> 'f list" where
  "layer_eval L below =
     map (\<lambda>z. const_at L z +
              sum_list (map (\<lambda>g. gate_contrib g below)
                            (filter (\<lambda>g. g_out g = z) (layer_gates L))))
         [0 ..< layer_width L]"

lemma length_layer_eval [simp]: "length (layer_eval L below) = layer_width L"
  by (simp add: layer_eval_def)

lemma layer_eval_nth:
  assumes "z < layer_width L"
  shows "layer_eval L below ! z =
           const_at L z +
           sum_list (map (\<lambda>g. gate_contrib g below)
                         (filter (\<lambda>g. g_out g = z) (layer_gates L)))"
  using assms by (simp add: layer_eval_def)

text \<open>
  All layer value vectors of one execution: output layer first, the input
  vector last (Rust: \<open>CircuitWitness::layer_values\<close> as produced by
  \<open>evaluate_circuit\<close>).
\<close>

fun circuit_values :: "'f::comm_ring_1 layer list \<Rightarrow> 'f list \<Rightarrow> 'f list list" where
  "circuit_values [] inputs = [inputs]"
| "circuit_values (L # Ls) inputs =
     (let rest = circuit_values Ls inputs in layer_eval L (hd rest) # rest)"

lemma circuit_values_nonempty: "circuit_values Ls inputs \<noteq> []"
  by (cases Ls) (auto simp: Let_def)

lemma length_circuit_values [simp]:
  "length (circuit_values Ls inputs) = length Ls + 1"
  by (induction Ls) (auto simp: Let_def)

text \<open>The output vector, and its foldr characterisation (spec form).\<close>

definition circuit_output :: "'f::comm_ring_1 layered_circuit \<Rightarrow> 'f list \<Rightarrow> 'f list" where
  "circuit_output C inputs = hd (circuit_values (circ_layers C) inputs)"

lemma circuit_output_foldr:
  "circuit_output C inputs = foldr layer_eval (circ_layers C) inputs"
proof -
  have "hd (circuit_values Ls inputs) = foldr layer_eval Ls inputs" for Ls :: "'a layer list"
    by (induction Ls) (auto simp: Let_def)
  then show ?thesis by (simp add: circuit_output_def)
qed

section \<open>Acceptance convention (seal point S-4)\<close>

text \<open>
  A circuit accepts an input vector iff EVERY output-layer wire evaluates
  to zero.  Compiled circuits encode their checks as residuals that vanish
  exactly when the constraint holds.
\<close>

definition circuit_accept :: "'f::comm_ring_1 layered_circuit \<Rightarrow> 'f list \<Rightarrow> bool" where
  "circuit_accept C inputs \<longleftrightarrow> (\<forall>v \<in> set (circuit_output C inputs). v = 0)"

section \<open>Sanity instance (non-vacuity witness)\<close>

text \<open>
  A tiny concrete circuit exercising all three gate kinds and a constant:
  one layer of width 2 over an input vector of width 2,

    out0 = 3*a + b*b*b - 5      (Lin + Pow3 + const)
    out1 = a*b                  (Mul)

  evaluated over the integers at (a, b) = (2, 1): out0 = 6 + 1 - 5 = 2,
  out1 = 2.  This pins the evaluator against off-by-one / orientation
  regressions and witnesses that the semantics is inhabited.
\<close>

definition demo_layer :: "int layer" where
  "demo_layer =
     \<lparr> layer_width_bits = 1,
       layer_gates =
         [ \<lparr> g_kind = GLin,  g_out = 0, g_in1 = 0, g_in2 = 0, g_coeff = 3 \<rparr>,
           \<lparr> g_kind = GPow3, g_out = 0, g_in1 = 1, g_in2 = 1, g_coeff = 1 \<rparr>,
           \<lparr> g_kind = GMul,  g_out = 1, g_in1 = 0, g_in2 = 1, g_coeff = 1 \<rparr> ],
       layer_consts = [(0, - 5)] \<rparr>"

definition demo_circuit :: "int layered_circuit" where
  "demo_circuit = \<lparr> circ_layers = [demo_layer], input_width_bits = 1 \<rparr>"

lemma demo_wf: "wf_circuit demo_circuit"
  by (simp add: wf_circuit_def demo_circuit_def demo_layer_def wf_layer_def
                wf_gate_def layer_width_def)

lemma demo_eval: "circuit_output demo_circuit [2, 1] = [2, 2]"
  by (simp add: circuit_output_def demo_circuit_def demo_layer_def Let_def
                layer_eval_def layer_width_def const_at_def gate_contrib_def
                upt_rec)

lemma demo_not_accepting: "\<not> circuit_accept demo_circuit [2, 1]"
  by (simp add: circuit_accept_def demo_eval)

text \<open>
  Acceptance is witnessed with a residual-style circuit: one Lin gate
  copying the input minus a constant, vanishing iff the input equals it
  (the shape compiled constraint circuits use, S-4).
\<close>

definition residual_circuit :: "int layered_circuit" where
  "residual_circuit =
     \<lparr> circ_layers =
         [ \<lparr> layer_width_bits = 0,
             layer_gates = [ \<lparr> g_kind = GLin, g_out = 0, g_in1 = 0, g_in2 = 0, g_coeff = 1 \<rparr> ],
             layer_consts = [(0, - 7)] \<rparr> ],
       input_width_bits = 0 \<rparr>"

lemma residual_accepts_exactly:
  "circuit_accept residual_circuit [x] \<longleftrightarrow> x = 7"
  by (simp add: circuit_accept_def circuit_output_def residual_circuit_def Let_def
                layer_eval_def layer_width_def const_at_def gate_contrib_def)

end
