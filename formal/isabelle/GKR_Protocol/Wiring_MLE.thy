(*
  Title:   Wiring_MLE.thy
  Session: GKR_Protocol (generic layer - no SMT / workload assumptions)

  Wiring-predicate MLEs: the table (materialized) oracle and the derived
  closed-form oracle, and the theorem that exact repartition of a layer's
  gate/const lists makes the two oracles equal AT EVERY EVALUATION POINT
  (lemma (c) of this development; see the modeling notes below).

  Rust refinement map (crate `ssgkr-protocol`, wiring.rs):
    wiring_term / gates_mle_eval ~ TableWiring::eval_predicate_mle
                                   (per-gate sparse contributions; unary
                                   kinds live on (z, x), the y block is
                                   used only by Mul)
    consts_mle_eval              ~ TableWiring::eval_const_mle
    side (Prog / Fixed)          ~ Side::{Prog, Fixed}
    side_wire                    ~ Side::wire  (block b, local offset off)
    gate_group / tap             ~ GateGroup (lin/pow3/mul taps merged into
                                   one kind-tagged tap list; same data)
    const_group                  ~ ConstGroup
    derived_layer                ~ DerivedLayer (groups + sparse remainder)
    expand_group / expand_gates  ~ DerivedRegularWiring::expand_gates
    expand_cgroup / expand_consts~ DerivedRegularWiring::expand_consts
    group_block                  ~ scalar * shifted_range_eq(terms, count)
                                   (the model keeps Fixed-side factors
                                   inside the block sum; they do not depend
                                   on the block index, so by distributivity
                                   this is the same field element as the
                                   hoisted `scalar` of the Rust code)
    group_template               ~ the local template sum T over tap offsets
    derived_eval                 ~ DerivedRegularWiring::eval_predicate_mle
    derived_const_eval           ~ DerivedRegularWiring::eval_const_mle
    srange (spec form)           ~ shifted_range_eq (the carry-DP algorithm
                                   is an O(log^2) evaluation strategy for
                                   this sum; the model uses the sum itself)

  Modeling notes:
  - Gates form a LIST; a duplicated gate tuple contributes twice.
    All equalities below are therefore stated up to MULTISET equality of
    gate lists, never set equality.
  - The theorem shape is "exact repartition => oracle equality":
    if re-expanding the derived groups plus the sparse remainder is a
    permutation of the layer's gate list (Rust pin:
    tests/verify_succinct.rs, `derivation_is_exact_repartition_of_the_
    circuit`), then the derived evaluation equals the table evaluation at
    every point (Rust pin: `derived_oracle_matches_table_on_compiled_
    circuits`).  The proof only re-associates one field sum, mirroring the
    correctness-model comment of `DerivedRegularWiring`.
  - Scope boundary: the `derive` ALGORITHM (hint fitting) is out of scope;
    wrong hints only degrade coverage, never correctness, because the
    sparse fallback is exact.  This theory treats a derived representation
    as GIVEN and proves that the repartition property alone forces
    equality of the two oracles.
  - The in-circuit meaning of the predicates (the GKR layer identity) is
    the business of GKR_Assembly, not of this theory.
*)

theory Wiring_MLE
  imports
    Layered_Circuit
    Multilinear_Extension
    "HOL-Library.Multiset"
begin

section \<open>Small sum and packing utilities\<close>

lemma sum_list_map_upt:
  fixes f :: "nat \<Rightarrow> 'f::comm_monoid_add"
  shows "sum_list (map f [0 ..< n]) = (\<Sum>b < n. f b)"
  by (induction n) simp_all

lemma sum_list_concat_map:
  fixes f :: "'a \<Rightarrow> 'f::comm_monoid_add"
  shows "sum_list (map f (concat xss)) = sum_list (map (\<lambda>xs. sum_list (map f xs)) xss)"
  by (induction xss) simp_all

lemma sum_list_concat:
  fixes xss :: "'f::comm_monoid_add list list"
  shows "sum_list (concat xss) = sum_list (map sum_list xss)"
  by (induction xss) simp_all

text \<open>Packing a pair of bounded indices into one index is injective and
  stays bounded - the arithmetic backbone of the tuple encodings below.\<close>

lemma pack_lt:
  fixes a A b B :: nat
  assumes "a < A" and "b < B"
  shows "a * B + b < A * B"
proof -
  have "a * B + b < (a + 1) * B" using assms(2) by simp
  also have "\<dots> \<le> A * B" using assms(1) by (intro mult_le_mono1) simp
  finally show ?thesis .
qed

lemma pack_inj:
  fixes a1 b1 a2 b2 B :: nat
  assumes "b1 < B" and "b2 < B"
  shows "a1 * B + b1 = a2 * B + b2 \<longleftrightarrow> a1 = a2 \<and> b1 = b2"
proof
  assume eq: "a1 * B + b1 = a2 * B + b2"
  have "b1 = (a1 * B + b1) mod B" using assms(1) by simp
  also have "\<dots> = b2" using eq assms(2) by simp
  finally have b: "b1 = b2" .
  moreover have "a1 = a2"
  proof -
    have "a1 = (a1 * B + b1) div B" using assms(1) by simp
    also have "\<dots> = a2" using eq assms(2) by simp
    finally show ?thesis .
  qed
  ultimately show "a1 = a2 \<and> b1 = b2" by simp
qed simp

section \<open>The Lagrange weight over a concatenated point\<close>

text \<open>
  The split identity: over a concatenated point the \<open>eq_pi\<close> weight of a
  packed index factors into the weights of the two halves.  This is the
  formal counterpart of the Rust comment on `DerivedRegularWiring`:
  "eq(z, ((A + b) << lb) + off) factors EXACTLY into eq(\<open>z_hi\<close>, A + b) *
  eq(\<open>z_lo\<close>, off) when offsets stay below the stride".
\<close>

lemma eq_pi_append:
  fixes p q :: "'f::comm_ring_1 list"
  assumes "i < 2 ^ length p" and "j < 2 ^ length q"
  shows "eq_pi (p @ q) (i * 2 ^ length q + j) = eq_pi p i * eq_pi q j"
  using assms(1)
proof (induction p arbitrary: i)
  case Nil
  then have "i = 0" by simp
  then show ?case by simp
next
  case (Cons a p)
  have jq: "j < 2 ^ length q" by (rule assms(2))
  show ?case
  proof (cases "i < 2 ^ length p")
    case True
    have lt: "i * 2 ^ length q + j < 2 ^ (length p + length q)"
    proof -
      have "i * 2 ^ length q + j < 2 ^ length p * 2 ^ length q"
        using True jq by (rule pack_lt)
      then show ?thesis by (simp add: power_add)
    qed
    have "eq_pi ((a # p) @ q) (i * 2 ^ length q + j)
          = eq_pi (a # (p @ q)) (i * 2 ^ length q + j)" by simp
    also have "\<dots> = (1 - a) * eq_pi (p @ q) (i * 2 ^ length q + j)"
      using eq_pi_cons_lo[of "i * 2 ^ length q + j" "p @ q" a] lt by simp
    also have "\<dots> = (1 - a) * (eq_pi p i * eq_pi q j)"
      using Cons.IH[OF True] by simp
    also have "\<dots> = eq_pi (a # p) i * eq_pi q j"
      using eq_pi_cons_lo[of i p a] True by (simp add: mult.assoc)
    finally show ?thesis .
  next
    case False
    define i' where "i' = i - 2 ^ length p"
    have ilt: "i' < 2 ^ length p"
      using Cons.prems False by (simp add: i'_def)
    have idec: "i = i' + 2 ^ length p"
      using False by (simp add: i'_def)
    have lt: "i' * 2 ^ length q + j < 2 ^ (length p + length q)"
    proof -
      have "i' * 2 ^ length q + j < 2 ^ length p * 2 ^ length q"
        using ilt jq by (rule pack_lt)
      then show ?thesis by (simp add: power_add)
    qed
    have shift: "i * 2 ^ length q + j = (i' * 2 ^ length q + j) + 2 ^ (length p + length q)"
      using idec by (simp add: power_add algebra_simps)
    have "eq_pi ((a # p) @ q) (i * 2 ^ length q + j)
          = eq_pi (a # (p @ q)) ((i' * 2 ^ length q + j) + 2 ^ length (p @ q))"
      by (simp add: shift)
    also have "\<dots> = a * eq_pi (p @ q) (i' * 2 ^ length q + j)"
      using eq_pi_cons_hi[of "i' * 2 ^ length q + j" "p @ q" a] lt by simp
    also have "\<dots> = a * (eq_pi p i' * eq_pi q j)"
      using Cons.IH[OF ilt] by simp
    also have "\<dots> = eq_pi (a # p) i * eq_pi q j"
      using eq_pi_cons_hi[of i' p a] ilt idec by (simp add: mult.assoc)
    finally show ?thesis .
  qed
qed

section \<open>Delta tables and their MLEs\<close>

lemma mle_delta:
  fixes c :: "'f::comm_ring_1"
  assumes "e < 2 ^ n"
  shows "mle n (\<lambda>idx. if idx = e then c else 0) pt = eq_pi pt e * c"
proof -
  have "mle n (\<lambda>idx. if idx = e then c else 0) pt
        = (\<Sum>idx < 2 ^ n. if idx = e then eq_pi pt e * c else 0)"
    unfolding mle_def by (intro sum.cong refl) auto
  also have "\<dots> = eq_pi pt e * c"
    using assms by simp
  finally show ?thesis .
qed

lemma mle_delta':
  fixes c :: "'f::comm_ring_1"
  assumes "e < 2 ^ n"
  shows "mle n (\<lambda>idx. if e = idx then c else 0) pt = eq_pi pt e * c"
proof -
  have "(\<lambda>idx. if e = idx then c else 0) = (\<lambda>idx. if idx = e then c else 0)"
    by (intro ext) auto
  then show ?thesis using mle_delta[OF assms] by simp
qed

section \<open>The gate-sum form of the wiring-predicate MLE (TableWiring)\<close>

text \<open>
  Per-gate contribution at an evaluation point, literally the loop body of
  \<open>TableWiring::eval_predicate_mle\<close>: coefficient times the output-wire and
  first-input-wire weights, times the second-input weight for the binary
  kind only (unary kinds live on \<open>(z, x)\<close>; their \<open>in2 = in1\<close> convention is
  irrelevant here because the factor is not consumed).
\<close>

definition wiring_term :: "gate_kind \<Rightarrow> 'f::comm_ring_1 list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f gate \<Rightarrow> 'f" where
  "wiring_term k z x y g =
     g_coeff g * eq_pi z (g_out g) * eq_pi x (g_in1 g) *
     (if k = GMul then eq_pi y (g_in2 g) else 1)"

definition gates_mle_eval :: "'f::comm_ring_1 gate list \<Rightarrow> gate_kind \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f" where
  "gates_mle_eval gs k z x y =
     sum_list (map (wiring_term k z x y) (filter (\<lambda>g. g_kind g = k) gs))"

lemma gates_mle_eval_Nil [simp]: "gates_mle_eval [] k z x y = 0"
  by (simp add: gates_mle_eval_def)

lemma gates_mle_eval_Cons:
  "gates_mle_eval (g # gs) k z x y =
     (if g_kind g = k then wiring_term k z x y g else 0) + gates_mle_eval gs k z x y"
  by (simp add: gates_mle_eval_def)

lemma gates_mle_eval_append:
  "gates_mle_eval (gs @ hs) k z x y = gates_mle_eval gs k z x y + gates_mle_eval hs k z x y"
  by (simp add: gates_mle_eval_def)

text \<open>The gate sum only depends on the MULTISET of gates: summation is
  invariant under repartition/permutation of the list (list semantics preserved -
  duplicated gates keep contributing twice on both sides).\<close>

lemma gates_mle_eval_mset_cong:
  assumes "mset gs = mset gs'"
  shows "gates_mle_eval gs k z x y = gates_mle_eval gs' k z x y"
proof -
  have "mset (map (wiring_term k z x y) (filter (\<lambda>g. g_kind g = k) gs))
      = mset (map (wiring_term k z x y) (filter (\<lambda>g. g_kind g = k) gs'))"
    using assms by (simp add: mset_filter mset_map)
  then show ?thesis
    unfolding gates_mle_eval_def by (metis sum_mset_sum_list)
qed

text \<open>Same shape for the additive-constant vector (TableWiring::\<open>eval_const_mle\<close>).\<close>

definition consts_mle_eval :: "(nat \<times> 'f::comm_ring_1) list \<Rightarrow> 'f list \<Rightarrow> 'f" where
  "consts_mle_eval cs z = sum_list (map (\<lambda>(w, v). v * eq_pi z w) cs)"

lemma consts_mle_eval_Nil [simp]: "consts_mle_eval [] z = 0"
  by (simp add: consts_mle_eval_def)

lemma consts_mle_eval_Cons:
  "consts_mle_eval ((w, v) # cs) z = v * eq_pi z w + consts_mle_eval cs z"
  by (simp add: consts_mle_eval_def)

lemma consts_mle_eval_append:
  "consts_mle_eval (cs @ ds) z = consts_mle_eval cs z + consts_mle_eval ds z"
  by (simp add: consts_mle_eval_def)

lemma consts_mle_eval_mset_cong:
  assumes "mset cs = mset cs'"
  shows "consts_mle_eval cs z = consts_mle_eval cs' z"
proof -
  have "mset (map (\<lambda>(w, v). v * eq_pi z w) cs) = mset (map (\<lambda>(w, v). v * eq_pi z w) cs')"
    using assms by (simp add: mset_map)
  then show ?thesis
    unfolding consts_mle_eval_def by (metis sum_mset_sum_list)
qed

section \<open>The definitional table MLE (tuple table, duplicates summed)\<close>

text \<open>
  The weighted wiring function on index tuples: at \<open>(z, x, y)\<close> it is the
  SUM of the coefficients of all gates of the given kind wired exactly to
  that tuple (duplicated tuples accumulate), and \<open>0\<close> elsewhere.  The
  binary kind lives on \<open>(z, x, y)\<close> triples, the unary kinds on \<open>(z, x)\<close>
  pairs.  Tuples are packed into one index (MSB-first, matching the
  variable order of concatenated points), and the definitional MLE is the
  \<open>mle\<close> of that table.
\<close>

definition enc3 :: "nat \<Rightarrow> 'f gate \<Rightarrow> nat" where
  "enc3 ib g = (g_out g * 2 ^ ib + g_in1 g) * 2 ^ ib + g_in2 g"

definition enc2 :: "nat \<Rightarrow> 'f gate \<Rightarrow> nat" where
  "enc2 ib g = g_out g * 2 ^ ib + g_in1 g"

definition table3 :: "nat \<Rightarrow> 'f::comm_ring_1 gate list \<Rightarrow> nat \<Rightarrow> 'f" where
  "table3 ib gs idx = sum_list (map g_coeff (filter (\<lambda>g. enc3 ib g = idx) gs))"

definition table2 :: "nat \<Rightarrow> 'f::comm_ring_1 gate list \<Rightarrow> nat \<Rightarrow> 'f" where
  "table2 ib gs idx = sum_list (map g_coeff (filter (\<lambda>g. enc2 ib g = idx) gs))"

lemma table3_Nil [simp]: "table3 ib [] idx = 0"
  by (simp add: table3_def)

lemma table3_Cons:
  "table3 ib (g # gs) idx = (if enc3 ib g = idx then g_coeff g else 0) + table3 ib gs idx"
  by (simp add: table3_def)

lemma table2_Nil [simp]: "table2 ib [] idx = 0"
  by (simp add: table2_def)

lemma table2_Cons:
  "table2 ib (g # gs) idx = (if enc2 ib g = idx then g_coeff g else 0) + table2 ib gs idx"
  by (simp add: table2_def)

text \<open>The packed table read at a packed in-range tuple is exactly the
  tuple sum: the coefficients of the gates wired to that tuple.\<close>

lemma table3_at_tuple:
  assumes x0: "x0 < 2 ^ ib" and y0: "y0 < 2 ^ ib"
      and wf: "\<forall>g \<in> set gs. g_in1 g < 2 ^ ib \<and> g_in2 g < 2 ^ ib"
  shows "table3 ib gs ((z0 * 2 ^ ib + x0) * 2 ^ ib + y0)
       = sum_list (map g_coeff
           (filter (\<lambda>g. g_out g = z0 \<and> g_in1 g = x0 \<and> g_in2 g = y0) gs))"
proof -
  have "filter (\<lambda>g. enc3 ib g = (z0 * 2 ^ ib + x0) * 2 ^ ib + y0) gs
      = filter (\<lambda>g. g_out g = z0 \<and> g_in1 g = x0 \<and> g_in2 g = y0) gs"
  proof (intro filter_cong refl)
    fix g assume gin: "g \<in> set gs"
    have gi1: "g_in1 g < 2 ^ ib" and gi2: "g_in2 g < 2 ^ ib"
      using wf gin by auto
    have inner: "g_out g * 2 ^ ib + g_in1 g = z0 * 2 ^ ib + x0
                 \<longleftrightarrow> g_out g = z0 \<and> g_in1 g = x0"
      using pack_inj[OF gi1 x0] .
    have "enc3 ib g = (z0 * 2 ^ ib + x0) * 2 ^ ib + y0
          \<longleftrightarrow> g_out g * 2 ^ ib + g_in1 g = z0 * 2 ^ ib + x0 \<and> g_in2 g = y0"
      unfolding enc3_def using pack_inj[OF gi2 y0] .
    then show "(enc3 ib g = (z0 * 2 ^ ib + x0) * 2 ^ ib + y0)
             = (g_out g = z0 \<and> g_in1 g = x0 \<and> g_in2 g = y0)"
      using inner by auto
  qed
  then show ?thesis by (simp add: table3_def)
qed

lemma table2_at_tuple:
  assumes x0: "x0 < 2 ^ ib"
      and wf: "\<forall>g \<in> set gs. g_in1 g < 2 ^ ib"
  shows "table2 ib gs (z0 * 2 ^ ib + x0)
       = sum_list (map g_coeff (filter (\<lambda>g. g_out g = z0 \<and> g_in1 g = x0) gs))"
proof -
  have "filter (\<lambda>g. enc2 ib g = z0 * 2 ^ ib + x0) gs
      = filter (\<lambda>g. g_out g = z0 \<and> g_in1 g = x0) gs"
  proof (intro filter_cong refl)
    fix g assume gin: "g \<in> set gs"
    have gi1: "g_in1 g < 2 ^ ib" using wf gin by auto
    show "(enc2 ib g = z0 * 2 ^ ib + x0) = (g_out g = z0 \<and> g_in1 g = x0)"
      unfolding enc2_def using pack_inj[OF gi1 x0] by auto
  qed
  then show ?thesis by (simp add: table2_def)
qed

text \<open>Range and split facts for the packed encodings.\<close>

lemma enc3_lt:
  assumes "g_out g < 2 ^ ob" "g_in1 g < 2 ^ ib" "g_in2 g < 2 ^ ib"
  shows "enc3 ib g < 2 ^ (ob + ib + ib)"
proof -
  have outer: "g_out g * 2 ^ ib + g_in1 g < 2 ^ ob * 2 ^ ib"
    using assms(1,2) by (rule pack_lt)
  have "(g_out g * 2 ^ ib + g_in1 g) * 2 ^ ib + g_in2 g < (2 ^ ob * 2 ^ ib) * 2 ^ ib"
    using outer assms(3) by (rule pack_lt)
  then show ?thesis by (simp add: enc3_def power_add)
qed

lemma enc2_lt:
  assumes "g_out g < 2 ^ ob" "g_in1 g < 2 ^ ib"
  shows "enc2 ib g < 2 ^ (ob + ib)"
  unfolding enc2_def using pack_lt[OF assms] by (simp add: power_add)

lemma enc3_split:
  "enc3 ib g = g_out g * 2 ^ (ib + ib) + (g_in1 g * 2 ^ ib + g_in2 g)"
  by (simp add: enc3_def power_add algebra_simps)

text \<open>The weight of a packed gate index over a concatenated point splits
  into the per-block weights (two applications of the split identity).\<close>

lemma eq_pi_enc3:
  fixes z x y :: "'f::comm_ring_1 list"
  assumes lz: "length z = ob" and lx: "length x = ib" and ly: "length y = ib"
      and go: "g_out g < 2 ^ ob" and g1: "g_in1 g < 2 ^ ib" and g2: "g_in2 g < 2 ^ ib"
  shows "eq_pi (z @ x @ y) (enc3 ib g)
       = eq_pi z (g_out g) * eq_pi x (g_in1 g) * eq_pi y (g_in2 g)"
proof -
  have inner_lt: "g_in1 g * 2 ^ ib + g_in2 g < 2 ^ (ib + ib)"
    using pack_lt[OF g1 g2] by (simp add: power_add)
  have "eq_pi (z @ x @ y) (enc3 ib g)
        = eq_pi (z @ x @ y) (g_out g * 2 ^ length (x @ y) + (g_in1 g * 2 ^ ib + g_in2 g))"
    by (simp add: enc3_split lx ly power_add)
  also have "\<dots> = eq_pi z (g_out g) * eq_pi (x @ y) (g_in1 g * 2 ^ ib + g_in2 g)"
    by (rule eq_pi_append) (use go lz lx ly inner_lt in \<open>simp_all add: power_add\<close>)
  also have "\<dots> = eq_pi z (g_out g) * (eq_pi x (g_in1 g) * eq_pi y (g_in2 g))"
    using eq_pi_append[of "g_in1 g" x "g_in2 g" y] g1 g2 lx ly by simp
  finally show ?thesis by (simp add: mult.assoc)
qed

lemma eq_pi_enc2:
  fixes z x :: "'f::comm_ring_1 list"
  assumes lz: "length z = ob" and lx: "length x = ib"
      and go: "g_out g < 2 ^ ob" and g1: "g_in1 g < 2 ^ ib"
  shows "eq_pi (z @ x) (enc2 ib g) = eq_pi z (g_out g) * eq_pi x (g_in1 g)"
  unfolding enc2_def
  using eq_pi_append[of "g_out g" z "g_in1 g" x] go g1 lz lx by simp

section \<open>The definitional MLE equals the gate sum (table oracle soundness)\<close>

text \<open>
  On a concatenated point the \<open>mle\<close> of the packed tuple table is exactly
  the per-gate sparse sum computed by the table oracle.  This discharges
  the FV-CONTRACT shape "the MLE agrees with the layer's weighted wiring"
  at the level of the definitional table.
\<close>

lemma table_mle3_gates:
  fixes z x y :: "'f::comm_ring_1 list"
  assumes wf: "\<forall>g \<in> set gs. g_kind g = GMul \<longrightarrow>
                 g_out g < 2 ^ ob \<and> g_in1 g < 2 ^ ib \<and> g_in2 g < 2 ^ ib"
      and lz: "length z = ob" and lx: "length x = ib" and ly: "length y = ib"
  shows "mle (ob + ib + ib) (table3 ib (filter (\<lambda>g. g_kind g = GMul) gs)) (z @ x @ y)
       = gates_mle_eval gs GMul z x y"
  using wf
proof (induction gs)
  case Nil
  have "table3 ib (filter (\<lambda>g. g_kind g = GMul) []) = (\<lambda>_. 0)" by (simp add: fun_eq_iff)
  then show ?case by (simp add: mle_zero)
next
  case (Cons g gs)
  have IH: "mle (ob + ib + ib) (table3 ib (filter (\<lambda>g. g_kind g = GMul) gs)) (z @ x @ y)
          = gates_mle_eval gs GMul z x y"
    using Cons by simp
  show ?case
  proof (cases "g_kind g = GMul")
    case False
    then show ?thesis using IH by (simp add: gates_mle_eval_Cons)
  next
    case True
    have go: "g_out g < 2 ^ ob" and g1: "g_in1 g < 2 ^ ib" and g2: "g_in2 g < 2 ^ ib"
      using Cons.prems True by auto
    have elt: "enc3 ib g < 2 ^ (ob + ib + ib)"
      by (rule enc3_lt[OF go g1 g2])
    have step: "mle (ob + ib + ib) (table3 ib (filter (\<lambda>g. g_kind g = GMul) (g # gs))) (z @ x @ y)
          = mle (ob + ib + ib) (\<lambda>idx. if enc3 ib g = idx then g_coeff g else 0) (z @ x @ y)
            + mle (ob + ib + ib) (table3 ib (filter (\<lambda>g. g_kind g = GMul) gs)) (z @ x @ y)"
    proof -
      have "mle (ob + ib + ib) (table3 ib (filter (\<lambda>g. g_kind g = GMul) (g # gs))) (z @ x @ y)
            = mle (ob + ib + ib)
                (\<lambda>idx. (if enc3 ib g = idx then g_coeff g else 0)
                       + table3 ib (filter (\<lambda>g. g_kind g = GMul) gs) idx) (z @ x @ y)"
        by (intro mle_cong) (simp add: True table3_Cons)
      also have "\<dots> = mle (ob + ib + ib) (\<lambda>idx. if enc3 ib g = idx then g_coeff g else 0) (z @ x @ y)
                      + mle (ob + ib + ib) (table3 ib (filter (\<lambda>g. g_kind g = GMul) gs)) (z @ x @ y)"
        by (rule mle_add)
      finally show ?thesis .
    qed
    have delta: "mle (ob + ib + ib) (\<lambda>idx. if enc3 ib g = idx then g_coeff g else 0) (z @ x @ y)
          = wiring_term GMul z x y g"
    proof -
      have "mle (ob + ib + ib) (\<lambda>idx. if enc3 ib g = idx then g_coeff g else 0) (z @ x @ y)
            = eq_pi (z @ x @ y) (enc3 ib g) * g_coeff g"
        by (rule mle_delta'[OF elt])
      also have "\<dots> = eq_pi z (g_out g) * eq_pi x (g_in1 g) * eq_pi y (g_in2 g) * g_coeff g"
        by (simp only: eq_pi_enc3[OF lz lx ly go g1 g2])
      finally show ?thesis
        by (simp add: wiring_term_def algebra_simps)
    qed
    show ?thesis
      using step delta IH True by (simp add: gates_mle_eval_Cons)
  qed
qed

lemma table_mle2_gates:
  fixes z x y :: "'f::comm_ring_1 list"
  assumes kk: "k = GLin \<or> k = GPow3"
      and wf: "\<forall>g \<in> set gs. g_kind g = k \<longrightarrow> g_out g < 2 ^ ob \<and> g_in1 g < 2 ^ ib"
      and lz: "length z = ob" and lx: "length x = ib"
  shows "mle (ob + ib) (table2 ib (filter (\<lambda>g. g_kind g = k) gs)) (z @ x)
       = gates_mle_eval gs k z x y"
  using wf
proof (induction gs)
  case Nil
  have "table2 ib (filter (\<lambda>g. g_kind g = k) []) = (\<lambda>_. 0)" by (simp add: fun_eq_iff)
  then show ?case by (simp add: mle_zero)
next
  case (Cons g gs)
  have IH: "mle (ob + ib) (table2 ib (filter (\<lambda>g. g_kind g = k) gs)) (z @ x)
          = gates_mle_eval gs k z x y"
    using Cons by simp
  have knm: "k \<noteq> GMul" using kk by auto
  show ?case
  proof (cases "g_kind g = k")
    case False
    then show ?thesis using IH by (simp add: gates_mle_eval_Cons)
  next
    case True
    have go: "g_out g < 2 ^ ob" and g1: "g_in1 g < 2 ^ ib"
      using Cons.prems True by auto
    have elt: "enc2 ib g < 2 ^ (ob + ib)"
      by (rule enc2_lt[OF go g1])
    have step: "mle (ob + ib) (table2 ib (filter (\<lambda>g. g_kind g = k) (g # gs))) (z @ x)
          = mle (ob + ib) (\<lambda>idx. if enc2 ib g = idx then g_coeff g else 0) (z @ x)
            + mle (ob + ib) (table2 ib (filter (\<lambda>g. g_kind g = k) gs)) (z @ x)"
    proof -
      have "mle (ob + ib) (table2 ib (filter (\<lambda>g. g_kind g = k) (g # gs))) (z @ x)
            = mle (ob + ib)
                (\<lambda>idx. (if enc2 ib g = idx then g_coeff g else 0)
                       + table2 ib (filter (\<lambda>g. g_kind g = k) gs) idx) (z @ x)"
        by (intro mle_cong) (simp add: True table2_Cons)
      also have "\<dots> = mle (ob + ib) (\<lambda>idx. if enc2 ib g = idx then g_coeff g else 0) (z @ x)
                      + mle (ob + ib) (table2 ib (filter (\<lambda>g. g_kind g = k) gs)) (z @ x)"
        by (rule mle_add)
      finally show ?thesis .
    qed
    have delta: "mle (ob + ib) (\<lambda>idx. if enc2 ib g = idx then g_coeff g else 0) (z @ x)
          = wiring_term k z x y g"
    proof -
      have "mle (ob + ib) (\<lambda>idx. if enc2 ib g = idx then g_coeff g else 0) (z @ x)
            = eq_pi (z @ x) (enc2 ib g) * g_coeff g"
        by (rule mle_delta'[OF elt])
      also have "\<dots> = eq_pi z (g_out g) * eq_pi x (g_in1 g) * g_coeff g"
        by (simp only: eq_pi_enc2[OF lz lx go g1])
      finally show ?thesis
        using knm by (simp add: wiring_term_def algebra_simps)
    qed
    show ?thesis
      using step delta IH True by (simp add: gates_mle_eval_Cons)
  qed
qed

text \<open>Constant vector: the definitional MLE of the accumulated-constant
  table (\<open>const_at\<close>, list semantics) is the sparse per-entry sum of
  the table oracle.\<close>

definition ctable :: "(nat \<times> 'f::comm_monoid_add) list \<Rightarrow> nat \<Rightarrow> 'f" where
  "ctable cs z = sum_list (map snd (filter (\<lambda>(w, c). w = z) cs))"

lemma ctable_Nil [simp]: "ctable [] z = 0"
  by (simp add: ctable_def)

lemma ctable_Cons:
  "ctable ((w, v) # cs) z = (if w = z then v else 0) + ctable cs z"
  by (simp add: ctable_def)

lemma const_at_ctable: "const_at L z = ctable (layer_consts L) z"
  by (simp add: const_at_def ctable_def)

lemma const_mle_eq:
  fixes z :: "'f::comm_ring_1 list"
  assumes wf: "\<forall>(w, v) \<in> set cs. w < 2 ^ ob"
      and lz: "length z = ob"
  shows "mle ob (ctable cs) z = consts_mle_eval cs z"
  using wf
proof (induction cs)
  case Nil
  have "ctable ([] :: (nat \<times> 'f) list) = (\<lambda>_. 0)" by (simp add: fun_eq_iff)
  then show ?case by (simp add: mle_zero)
next
  case (Cons wv cs)
  obtain w v where wv: "wv = (w, v)" by (cases wv)
  have wlt: "w < 2 ^ ob" using Cons.prems wv by auto
  have IH: "mle ob (ctable cs) z = consts_mle_eval cs z" using Cons by simp
  have "mle ob (ctable ((w, v) # cs)) z
        = mle ob (\<lambda>z0. (if w = z0 then v else 0) + ctable cs z0) z"
    by (intro mle_cong) (simp add: ctable_Cons)
  also have "\<dots> = mle ob (\<lambda>z0. if w = z0 then v else 0) z + mle ob (ctable cs) z"
    by (rule mle_add)
  also have "\<dots> = v * eq_pi z w + consts_mle_eval cs z"
    using mle_delta'[OF wlt, of v z] lz IH by (simp add: algebra_simps)
  finally show ?case using wv by (simp add: consts_mle_eval_Cons)
qed

section \<open>The derived closed-form representation (DerivedRegularWiring)\<close>

text \<open>
  One SIDE of a derived family: block \<open>b\<close>'s wire at local offset \<open>off\<close> is
  \<open>(base_hi + b) * 2 ^ lb + off\<close> (an aligned arithmetic progression with
  stride \<open>2 ^ lb\<close>), or one fixed wire shared by every block (the
  degenerate progression).  Literally \<open>Side::{Prog, Fixed}\<close> of wiring.rs.
\<close>

datatype side =
    Prog nat nat    \<comment> \<open>\<open>Prog base_hi lb\<close>\<close>
  | Fixed nat       \<comment> \<open>\<open>Fixed wire\<close>\<close>

fun side_lb :: "side \<Rightarrow> nat" where
  "side_lb (Prog bh lb) = lb"
| "side_lb (Fixed w) = 0"

fun side_wire :: "side \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "side_wire (Prog bh lb) b off = (bh + b) * 2 ^ lb + off"
| "side_wire (Fixed w) b off = w"

text \<open>
  One derived gate family: \<open>count\<close> blocks whose taps follow the group's
  side progressions.  The Rust \<open>GateGroup\<close> keeps three kind-homogeneous
  tap vectors (lin / pow3 / mul); the model merges them into one
  kind-tagged tap list, which carries the same data (the split is a Rust
  layout convenience).  A unary tap re-uses its \<open>in1\<close> wire as \<open>in2\<close> on
  expansion, exactly like \<open>expand_gates\<close> (\<open>in2: in1\<close>).
\<close>

record 'f tap =
  tap_kind  :: gate_kind
  tap_out   :: nat
  tap_in1   :: nat
  tap_in2   :: nat
  tap_coeff :: 'f

record 'f gate_group =
  grp_count :: nat
  grp_out   :: side
  grp_in1   :: side
  grp_in2   :: side
  grp_taps  :: "'f tap list"

record 'f const_group =
  cg_count :: nat
  cg_out   :: side
  cg_vals  :: "(nat \<times> 'f) list"

record 'f derived_layer =
  drv_groups  :: "'f gate_group list"
  drv_sparse  :: "'f gate list"
  drv_cgroups :: "'f const_group list"
  drv_csparse :: "(nat \<times> 'f) list"

subsection \<open>Re-expansion (the audit helper \<open>expand_gates\<close> / \<open>expand_consts\<close>)\<close>

definition tap_gate :: "'f gate_group \<Rightarrow> nat \<Rightarrow> 'f tap \<Rightarrow> 'f gate" where
  "tap_gate G b t =
     \<lparr> g_kind = tap_kind t,
       g_out  = side_wire (grp_out G) b (tap_out t),
       g_in1  = side_wire (grp_in1 G) b (tap_in1 t),
       g_in2  = (if tap_kind t = GMul then side_wire (grp_in2 G) b (tap_in2 t)
                 else side_wire (grp_in1 G) b (tap_in1 t)),
       g_coeff = tap_coeff t \<rparr>"

lemma tap_gate_sel [simp]:
  "g_kind (tap_gate G b t) = tap_kind t"
  "g_out (tap_gate G b t) = side_wire (grp_out G) b (tap_out t)"
  "g_in1 (tap_gate G b t) = side_wire (grp_in1 G) b (tap_in1 t)"
  "g_coeff (tap_gate G b t) = tap_coeff t"
  by (simp_all add: tap_gate_def)

lemma tap_gate_in2_mul [simp]:
  "tap_kind t = GMul \<Longrightarrow> g_in2 (tap_gate G b t) = side_wire (grp_in2 G) b (tap_in2 t)"
  by (simp add: tap_gate_def)

definition expand_group :: "'f gate_group \<Rightarrow> 'f gate list" where
  "expand_group G = concat (map (\<lambda>b. map (tap_gate G b) (grp_taps G)) [0 ..< grp_count G])"

definition expand_gates :: "'f derived_layer \<Rightarrow> 'f gate list" where
  "expand_gates D = concat (map expand_group (drv_groups D)) @ drv_sparse D"

definition expand_cgroup :: "'f const_group \<Rightarrow> (nat \<times> 'f) list" where
  "expand_cgroup CG =
     concat (map (\<lambda>b. map (\<lambda>(u, v). (side_wire (cg_out CG) b u, v)) (cg_vals CG))
                 [0 ..< cg_count CG])"

definition expand_consts :: "'f derived_layer \<Rightarrow> (nat \<times> 'f) list" where
  "expand_consts D = concat (map expand_cgroup (drv_cgroups D)) @ drv_csparse D"

subsection \<open>Well-formedness of a derived representation\<close>

text \<open>
  \<open>wf_side n cnt s\<close>: on a progression side, the local width fits in the
  point and every enumerated high index is representable - literally the
  Rust requirement \<open>bases[t] + count <= 2^{points[t].len()}\<close> of
  \<open>shifted_range_eq\<close>.  \<open>tap_off_ok\<close>: offsets stay below the stride (the
  factorization condition).  Fixed sides need nothing: both the expansion
  and the evaluation ignore the offset there.
\<close>

fun wf_side :: "nat \<Rightarrow> nat \<Rightarrow> side \<Rightarrow> bool" where
  "wf_side n cnt (Prog bh lb) \<longleftrightarrow> lb \<le> n \<and> bh + cnt \<le> 2 ^ (n - lb)"
| "wf_side n cnt (Fixed w) \<longleftrightarrow> True"

fun tap_off_ok :: "side \<Rightarrow> nat \<Rightarrow> bool" where
  "tap_off_ok (Prog bh lb) u \<longleftrightarrow> u < 2 ^ lb"
| "tap_off_ok (Fixed w) u \<longleftrightarrow> True"

definition wf_group :: "nat \<Rightarrow> nat \<Rightarrow> 'f gate_group \<Rightarrow> bool" where
  "wf_group ob ib G \<longleftrightarrow>
     wf_side ob (grp_count G) (grp_out G) \<and>
     wf_side ib (grp_count G) (grp_in1 G) \<and>
     wf_side ib (grp_count G) (grp_in2 G) \<and>
     (\<forall>t \<in> set (grp_taps G).
        tap_off_ok (grp_out G) (tap_out t) \<and>
        tap_off_ok (grp_in1 G) (tap_in1 t) \<and>
        (tap_kind t = GMul \<longrightarrow> tap_off_ok (grp_in2 G) (tap_in2 t)))"

definition wf_cgroup :: "nat \<Rightarrow> 'f const_group \<Rightarrow> bool" where
  "wf_cgroup ob CG \<longleftrightarrow>
     wf_side ob (cg_count CG) (cg_out CG) \<and>
     (\<forall>(u, v) \<in> set (cg_vals CG). tap_off_ok (cg_out CG) u)"

definition wf_derived :: "nat \<Rightarrow> nat \<Rightarrow> 'f derived_layer \<Rightarrow> bool" where
  "wf_derived ob ib D \<longleftrightarrow>
     (\<forall>G \<in> set (drv_groups D). wf_group ob ib G) \<and>
     (\<forall>CG \<in> set (drv_cgroups D). wf_cgroup ob CG)"

subsection \<open>Closed-form evaluation (the derived oracle)\<close>

text \<open>
  Block-matching factor of one side at block \<open>b\<close>: the \<open>eq_pi\<close> weight of
  the high part on a progression side (one term of the shifted-range sum),
  or the full-point weight of the shared wire on a fixed side (the Rust
  \<open>scalar\<close>; block-independent, kept inside the block sum here - the same
  element by distributivity).
\<close>

fun side_block_eq :: "'f::comm_ring_1 list \<Rightarrow> side \<Rightarrow> nat \<Rightarrow> 'f" where
  "side_block_eq pt (Prog bh lb) b = eq_pi (take (length pt - lb) pt) (bh + b)"
| "side_block_eq pt (Fixed w) b = eq_pi pt w"

definition side_lo_pt :: "'f list \<Rightarrow> side \<Rightarrow> 'f list" where
  "side_lo_pt pt s = drop (length pt - side_lb s) pt"

text \<open>The specification form of \<open>shifted_range_eq\<close>: the sum over the block
  range of the product of per-term high-part weights.  The Rust carry-DP is
  an \<open>O(log^2)\<close> evaluation strategy for exactly this sum (pinned executable
  by \<open>shifted_range_eq_matches_bruteforce\<close>); the model consumes the sum.\<close>

definition group_block :: "'f::comm_ring_1 gate_group \<Rightarrow> bool \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f" where
  "group_block G binp z x y =
     (\<Sum>b < grp_count G.
        side_block_eq z (grp_out G) b * side_block_eq x (grp_in1 G) b *
        (if binp then side_block_eq y (grp_in2 G) b else 1))"

definition tap_term :: "gate_kind \<Rightarrow> 'f::comm_ring_1 gate_group \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f tap \<Rightarrow> 'f" where
  "tap_term k G z x y t =
     tap_coeff t * eq_pi (side_lo_pt z (grp_out G)) (tap_out t)
                 * eq_pi (side_lo_pt x (grp_in1 G)) (tap_in1 t)
                 * (if k = GMul then eq_pi (side_lo_pt y (grp_in2 G)) (tap_in2 t) else 1)"

definition group_template :: "gate_kind \<Rightarrow> 'f::comm_ring_1 gate_group \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f" where
  "group_template k G z x y =
     sum_list (map (tap_term k G z x y) (filter (\<lambda>t. tap_kind t = k) (grp_taps G)))"

definition derived_eval :: "'f::comm_ring_1 derived_layer \<Rightarrow> gate_kind \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f" where
  "derived_eval D k z x y =
     sum_list (map (\<lambda>G. group_block G (k = GMul) z x y * group_template k G z x y)
                   (drv_groups D))
     + gates_mle_eval (drv_sparse D) k z x y"

definition cgroup_eval :: "'f::comm_ring_1 const_group \<Rightarrow> 'f list \<Rightarrow> 'f" where
  "cgroup_eval CG z =
     (\<Sum>b < cg_count CG. side_block_eq z (cg_out CG) b) *
     sum_list (map (\<lambda>(u, v). v * eq_pi (side_lo_pt z (cg_out CG)) u) (cg_vals CG))"

definition derived_const_eval :: "'f::comm_ring_1 derived_layer \<Rightarrow> 'f list \<Rightarrow> 'f" where
  "derived_const_eval D z =
     sum_list (map (\<lambda>CG. cgroup_eval CG z) (drv_cgroups D))
     + consts_mle_eval (drv_csparse D) z"

section \<open>Re-association: the closed form equals the expanded gate sum\<close>

text \<open>The per-wire split (the Rust correctness comment, made a lemma): the weight of a
  progression wire factors into block part times local part.\<close>

lemma side_eq_split:
  fixes pt :: "'f::comm_ring_1 list"
  assumes ws: "wf_side (length pt) cnt s"
      and b: "b < cnt"
      and u: "tap_off_ok s u"
  shows "eq_pi pt (side_wire s b u) = side_block_eq pt s b * eq_pi (side_lo_pt pt s) u"
proof (cases s)
  case (Fixed w)
  then show ?thesis by (simp add: side_lo_pt_def)
next
  case (Prog bh lb)
  have lb_le: "lb \<le> length pt" and range: "bh + cnt \<le> 2 ^ (length pt - lb)"
    using ws Prog by simp_all
  have b_lt: "bh + b < 2 ^ (length pt - lb)" using b range by simp
  have u_lt: "u < 2 ^ lb" using u Prog by simp
  have len_take: "length (take (length pt - lb) pt) = length pt - lb"
    using lb_le by simp
  have len_drop: "length (drop (length pt - lb) pt) = lb"
    using lb_le by simp
  have "eq_pi pt ((bh + b) * 2 ^ lb + u)
        = eq_pi (take (length pt - lb) pt @ drop (length pt - lb) pt)
                ((bh + b) * 2 ^ length (drop (length pt - lb) pt) + u)"
    using lb_le by simp
  also have "\<dots> = eq_pi (take (length pt - lb) pt) (bh + b)
                  * eq_pi (drop (length pt - lb) pt) u"
    by (rule eq_pi_append) (use b_lt u_lt len_take len_drop in simp_all)
  finally show ?thesis
    using Prog by (simp add: side_lo_pt_def)
qed

text \<open>Per-tap re-association: one expanded gate's sparse term is the block
  factor times the local template term.\<close>

lemma wiring_term_tap:
  fixes z x y :: "'f::comm_ring_1 list"
  assumes wo: "wf_side (length z) (grp_count G) (grp_out G)"
      and w1: "wf_side (length x) (grp_count G) (grp_in1 G)"
      and w2: "wf_side (length y) (grp_count G) (grp_in2 G)"
      and b: "b < grp_count G"
      and uo: "tap_off_ok (grp_out G) (tap_out t)"
      and u1: "tap_off_ok (grp_in1 G) (tap_in1 t)"
      and u2: "tap_kind t = GMul \<Longrightarrow> tap_off_ok (grp_in2 G) (tap_in2 t)"
      and kt: "tap_kind t = k"
  shows "wiring_term k z x y (tap_gate G b t)
       = (side_block_eq z (grp_out G) b * side_block_eq x (grp_in1 G) b *
          (if k = GMul then side_block_eq y (grp_in2 G) b else 1))
         * tap_term k G z x y t"
proof (cases "k = GMul")
  case True
  have so: "eq_pi z (side_wire (grp_out G) b (tap_out t))
          = side_block_eq z (grp_out G) b * eq_pi (side_lo_pt z (grp_out G)) (tap_out t)"
    by (rule side_eq_split[OF wo b uo])
  have s1: "eq_pi x (side_wire (grp_in1 G) b (tap_in1 t))
          = side_block_eq x (grp_in1 G) b * eq_pi (side_lo_pt x (grp_in1 G)) (tap_in1 t)"
    by (rule side_eq_split[OF w1 b u1])
  have s2: "eq_pi y (side_wire (grp_in2 G) b (tap_in2 t))
          = side_block_eq y (grp_in2 G) b * eq_pi (side_lo_pt y (grp_in2 G)) (tap_in2 t)"
    by (rule side_eq_split[OF w2 b u2]) (use kt True in simp)
  show ?thesis
    using True kt
    by (simp add: wiring_term_def tap_term_def so s1 s2 algebra_simps)
next
  case False
  have so: "eq_pi z (side_wire (grp_out G) b (tap_out t))
          = side_block_eq z (grp_out G) b * eq_pi (side_lo_pt z (grp_out G)) (tap_out t)"
    by (rule side_eq_split[OF wo b uo])
  have s1: "eq_pi x (side_wire (grp_in1 G) b (tap_in1 t))
          = side_block_eq x (grp_in1 G) b * eq_pi (side_lo_pt x (grp_in1 G)) (tap_in1 t)"
    by (rule side_eq_split[OF w1 b u1])
  show ?thesis
    using False kt
    by (simp add: wiring_term_def tap_term_def so s1 algebra_simps)
qed

text \<open>Group-level re-association: summing the expanded gates of one group
  IS the product of its block factor and its local template sum - the
  derived oracle only re-associates the table oracle's field sum.\<close>

lemma group_eval_expand:
  fixes z x y :: "'f::comm_ring_1 list"
  assumes wf: "wf_group (length z) (length x) G"
      and ly: "length y = length x"
  shows "gates_mle_eval (expand_group G) k z x y
       = group_block G (k = GMul) z x y * group_template k G z x y"
proof -
  let ?B = "\<lambda>b. side_block_eq z (grp_out G) b * side_block_eq x (grp_in1 G) b *
                 (if k = GMul then side_block_eq y (grp_in2 G) b else 1)"
  have wo: "wf_side (length z) (grp_count G) (grp_out G)"
   and w1: "wf_side (length x) (grp_count G) (grp_in1 G)"
   and w2: "wf_side (length y) (grp_count G) (grp_in2 G)"
    using wf ly by (simp_all add: wf_group_def)
  have taps: "\<forall>t \<in> set (grp_taps G).
        tap_off_ok (grp_out G) (tap_out t) \<and>
        tap_off_ok (grp_in1 G) (tap_in1 t) \<and>
        (tap_kind t = GMul \<longrightarrow> tap_off_ok (grp_in2 G) (tap_in2 t))"
    using wf by (simp add: wf_group_def)
  have "gates_mle_eval (expand_group G) k z x y
        = sum_list (map (\<lambda>b. gates_mle_eval (map (tap_gate G b) (grp_taps G)) k z x y)
                        [0 ..< grp_count G])"
    unfolding expand_group_def gates_mle_eval_def
    by (simp add: filter_concat map_concat sum_list_concat sum_list_concat_map o_def)
  also have "\<dots> = sum_list (map (\<lambda>b. ?B b * group_template k G z x y) [0 ..< grp_count G])"
  proof (intro arg_cong[of _ _ sum_list] map_cong refl)
    fix b assume "b \<in> set [0 ..< grp_count G]"
    then have blt: "b < grp_count G" by simp
    have "gates_mle_eval (map (tap_gate G b) (grp_taps G)) k z x y
          = sum_list (map (wiring_term k z x y \<circ> tap_gate G b)
                          (filter (\<lambda>t. tap_kind t = k) (grp_taps G)))"
      unfolding gates_mle_eval_def
      by (simp add: filter_map o_def)
    also have "\<dots> = sum_list (map (\<lambda>t. ?B b * tap_term k G z x y t)
                                  (filter (\<lambda>t. tap_kind t = k) (grp_taps G)))"
    proof (intro arg_cong[of _ _ sum_list] map_cong refl)
      fix t assume tin: "t \<in> set (filter (\<lambda>t. tap_kind t = k) (grp_taps G))"
      then have tset: "t \<in> set (grp_taps G)" and tk: "tap_kind t = k" by auto
      show "(wiring_term k z x y \<circ> tap_gate G b) t = ?B b * tap_term k G z x y t"
        using wiring_term_tap[OF wo w1 w2 blt _ _ _ tk] taps tset by (simp add: o_def)
    qed
    also have "\<dots> = ?B b * group_template k G z x y"
      unfolding group_template_def by (simp add: sum_list_const_mult)
    finally show "gates_mle_eval (map (tap_gate G b) (grp_taps G)) k z x y
                = ?B b * group_template k G z x y" .
  qed
  also have "\<dots> = (\<Sum>b < grp_count G. ?B b * group_template k G z x y)"
    by (simp add: sum_list_map_upt)
  also have "\<dots> = (\<Sum>b < grp_count G. ?B b) * group_template k G z x y"
    by (simp add: sum_distrib_right)
  also have "\<dots> = group_block G (k = GMul) z x y * group_template k G z x y"
    by (simp add: group_block_def)
  finally show ?thesis .
qed

lemma cgroup_eval_expand:
  fixes z :: "'f::comm_ring_1 list"
  assumes wf: "wf_cgroup (length z) CG"
  shows "consts_mle_eval (expand_cgroup CG) z = cgroup_eval CG z"
proof -
  let ?B = "\<lambda>b. side_block_eq z (cg_out CG) b"
  let ?T = "sum_list (map (\<lambda>(u, v). v * eq_pi (side_lo_pt z (cg_out CG)) u) (cg_vals CG))"
  have wo: "wf_side (length z) (cg_count CG) (cg_out CG)"
    using wf by (simp add: wf_cgroup_def)
  have offs: "\<forall>(u, v) \<in> set (cg_vals CG). tap_off_ok (cg_out CG) u"
    using wf by (simp add: wf_cgroup_def)
  have "consts_mle_eval (expand_cgroup CG) z
        = sum_list (map (\<lambda>b. consts_mle_eval
                              (map (\<lambda>(u, v). (side_wire (cg_out CG) b u, v)) (cg_vals CG)) z)
                        [0 ..< cg_count CG])"
    unfolding expand_cgroup_def consts_mle_eval_def
    by (simp add: map_concat sum_list_concat sum_list_concat_map o_def case_prod_unfold)
  also have "\<dots> = sum_list (map (\<lambda>b. ?B b * ?T) [0 ..< cg_count CG])"
  proof (intro arg_cong[of _ _ sum_list] map_cong refl)
    fix b assume "b \<in> set [0 ..< cg_count CG]"
    then have blt: "b < cg_count CG" by simp
    have "consts_mle_eval (map (\<lambda>(u, v). (side_wire (cg_out CG) b u, v)) (cg_vals CG)) z
          = sum_list (map (\<lambda>(u, v). v * eq_pi z (side_wire (cg_out CG) b u)) (cg_vals CG))"
      unfolding consts_mle_eval_def
      by (simp add: o_def case_prod_unfold)
    also have "\<dots> = sum_list (map (\<lambda>(u, v). ?B b * (v * eq_pi (side_lo_pt z (cg_out CG)) u))
                                  (cg_vals CG))"
    proof (intro arg_cong[of _ _ sum_list] map_cong refl)
      fix uv assume uvin: "uv \<in> set (cg_vals CG)"
      obtain u v where uv: "uv = (u, v)" by (cases uv)
      have uok: "tap_off_ok (cg_out CG) u" using offs uvin uv by auto
      show "(case uv of (u, v) \<Rightarrow> v * eq_pi z (side_wire (cg_out CG) b u))
          = (case uv of (u, v) \<Rightarrow> ?B b * (v * eq_pi (side_lo_pt z (cg_out CG)) u))"
        using side_eq_split[OF wo blt uok] uv by (simp add: algebra_simps)
    qed
    also have "\<dots> = ?B b * ?T"
      by (simp add: sum_list_const_mult case_prod_unfold)
    finally show "consts_mle_eval (map (\<lambda>(u, v). (side_wire (cg_out CG) b u, v)) (cg_vals CG)) z
                = ?B b * ?T" .
  qed
  also have "\<dots> = (\<Sum>b < cg_count CG. ?B b * ?T)"
    by (simp add: sum_list_map_upt)
  also have "\<dots> = (\<Sum>b < cg_count CG. ?B b) * ?T"
    by (simp add: sum_distrib_right)
  finally show ?thesis by (simp add: cgroup_eval_def)
qed

text \<open>Layer-level re-association: the derived oracle equals the sparse
  gate sum of its own re-expansion.\<close>

lemma derived_eval_expand:
  fixes z x y :: "'f::comm_ring_1 list"
  assumes wf: "\<forall>G \<in> set (drv_groups D). wf_group (length z) (length x) G"
      and ly: "length y = length x"
  shows "derived_eval D k z x y = gates_mle_eval (expand_gates D) k z x y"
proof -
  have "gates_mle_eval (concat (map expand_group (drv_groups D))) k z x y
        = sum_list (map (\<lambda>G. gates_mle_eval (expand_group G) k z x y) (drv_groups D))"
    unfolding gates_mle_eval_def
    by (simp add: filter_concat map_concat sum_list_concat sum_list_concat_map o_def)
  also have "\<dots> = sum_list (map (\<lambda>G. group_block G (k = GMul) z x y * group_template k G z x y)
                                (drv_groups D))"
    using wf by (intro arg_cong[of _ _ sum_list] map_cong refl)
               (simp add: group_eval_expand ly)
  finally show ?thesis
    by (simp add: derived_eval_def expand_gates_def gates_mle_eval_append)
qed

lemma derived_const_eval_expand:
  fixes z :: "'f::comm_ring_1 list"
  assumes wf: "\<forall>CG \<in> set (drv_cgroups D). wf_cgroup (length z) CG"
  shows "derived_const_eval D z = consts_mle_eval (expand_consts D) z"
proof -
  have "consts_mle_eval (concat (map expand_cgroup (drv_cgroups D))) z
        = sum_list (map (\<lambda>CG. consts_mle_eval (expand_cgroup CG) z) (drv_cgroups D))"
    unfolding consts_mle_eval_def
    by (simp add: map_concat sum_list_concat sum_list_concat_map o_def)
  also have "\<dots> = sum_list (map (\<lambda>CG. cgroup_eval CG z) (drv_cgroups D))"
    using wf by (intro arg_cong[of _ _ sum_list] map_cong refl) (simp add: cgroup_eval_expand)
  finally show ?thesis
    by (simp add: derived_const_eval_def expand_consts_def consts_mle_eval_append)
qed

section \<open>Main theorem: exact repartition forces oracle equality (lemma (c))\<close>

text \<open>
  If re-expanding the derived representation reproduces the layer's gate
  list AS A MULTISET (the exact-repartition property, Rust pin 2 of
  tests/\<open>verify_succinct\<close>.rs), then the derived closed-form oracle and the
  table oracle agree AT EVERY EVALUATION POINT (Rust pin 1) - for every
  gate kind, and likewise for the constant vector.  Wrong or missing
  layout hints change only which side of the repartition a gate lands on,
  never this equality (hints are soundness-inert).
\<close>

theorem derived_mle_eq_table:
  fixes z x y :: "'f::comm_ring_1 list"
  assumes repart: "mset (expand_gates D) = mset (layer_gates L)"
      and wf: "\<forall>G \<in> set (drv_groups D). wf_group (length z) (length x) G"
      and ly: "length y = length x"
  shows "derived_eval D k z x y = gates_mle_eval (layer_gates L) k z x y"
proof -
  have "derived_eval D k z x y = gates_mle_eval (expand_gates D) k z x y"
    by (rule derived_eval_expand[OF wf ly])
  also have "\<dots> = gates_mle_eval (layer_gates L) k z x y"
    by (rule gates_mle_eval_mset_cong[OF repart])
  finally show ?thesis .
qed

theorem derived_const_mle_eq_table:
  fixes z :: "'f::comm_ring_1 list"
  assumes repart: "mset (expand_consts D) = mset (layer_consts L)"
      and wf: "\<forall>CG \<in> set (drv_cgroups D). wf_cgroup (length z) CG"
  shows "derived_const_eval D z = consts_mle_eval (layer_consts L) z"
proof -
  have "derived_const_eval D z = consts_mle_eval (expand_consts D) z"
    by (rule derived_const_eval_expand[OF wf])
  also have "\<dots> = consts_mle_eval (layer_consts L) z"
    by (rule consts_mle_eval_mset_cong[OF repart])
  finally show ?thesis .
qed

text \<open>Corollaries against the DEFINITIONAL table MLE (the \<open>mle\<close> of the
  tuple table): the derived oracle computes the same polynomial, at
  every point, for the binary kind, the unary kinds, and the constants.\<close>

corollary derived_eval_is_table_mle3:
  fixes z x y :: "'f::comm_ring_1 list"
  assumes repart: "mset (expand_gates D) = mset (layer_gates L)"
      and wf: "\<forall>G \<in> set (drv_groups D). wf_group ob ib G"
      and wfl: "\<forall>g \<in> set (layer_gates L). g_kind g = GMul \<longrightarrow>
                  g_out g < 2 ^ ob \<and> g_in1 g < 2 ^ ib \<and> g_in2 g < 2 ^ ib"
      and lz: "length z = ob" and lx: "length x = ib" and ly: "length y = ib"
  shows "derived_eval D GMul z x y
       = mle (ob + ib + ib) (table3 ib (filter (\<lambda>g. g_kind g = GMul) (layer_gates L))) (z @ x @ y)"
  using derived_mle_eq_table[of D L z x y GMul] table_mle3_gates[OF wfl lz lx ly]
        repart wf lz lx ly by simp

corollary derived_eval_is_table_mle2:
  fixes z x y :: "'f::comm_ring_1 list"
  assumes kk: "k = GLin \<or> k = GPow3"
      and repart: "mset (expand_gates D) = mset (layer_gates L)"
      and wf: "\<forall>G \<in> set (drv_groups D). wf_group ob ib G"
      and wfl: "\<forall>g \<in> set (layer_gates L). g_kind g = k \<longrightarrow>
                  g_out g < 2 ^ ob \<and> g_in1 g < 2 ^ ib"
      and lz: "length z = ob" and lx: "length x = ib" and ly: "length y = ib"
  shows "derived_eval D k z x y
       = mle (ob + ib) (table2 ib (filter (\<lambda>g. g_kind g = k) (layer_gates L))) (z @ x)"
  using derived_mle_eq_table[of D L z x y k] table_mle2_gates[OF kk wfl lz lx, of y]
        repart wf lz lx ly by simp

corollary derived_const_eval_is_const_mle:
  fixes z :: "'f::comm_ring_1 list"
  assumes repart: "mset (expand_consts D) = mset (layer_consts L)"
      and wf: "\<forall>CG \<in> set (drv_cgroups D). wf_cgroup ob CG"
      and wfl: "\<forall>(w, v) \<in> set (layer_consts L). w < 2 ^ ob"
      and lz: "length z = ob"
  shows "derived_const_eval D z = mle ob (const_at L) z"
proof -
  have "mle ob (const_at L) z = mle ob (ctable (layer_consts L)) z"
    by (intro mle_cong) (simp add: const_at_ctable)
  also have "\<dots> = consts_mle_eval (layer_consts L) z"
    by (rule const_mle_eq[OF wfl lz])
  finally show ?thesis
    using derived_const_mle_eq_table[OF repart] wf lz by simp
qed

section \<open>Uniform-block closed form (the \<open>shifted_range_eq\<close> specification lemma)\<close>

text \<open>
  The full-range two-term instance of the shifted-range sum has the
  product closed form the Rust code calls \<open>eq_points\<close>: summing the
  diagonal weights over the whole cube collapses to a per-variable
  product.  (This is the \<open>with all bases zero and count = 2^m\<close> reduction
  of the wiring.rs module doc; the partial-range carry-DP closed form
  itself is an evaluation algorithm, out of the model's scope.)
\<close>

lemma srange_full_two_terms:
  fixes p q :: "'f::comm_ring_1 list"
  assumes "length p = length q"
  shows "(\<Sum>b < 2 ^ length p. eq_pi p b * eq_pi q b)
       = (\<Prod>j < length p. p ! j * q ! j + (1 - p ! j) * (1 - q ! j))"
  using assms
proof (induction p q rule: list_induct2)
  case Nil
  show ?case by simp
next
  case (Cons a p c q)
  have lpq: "length p = length q" by fact
  have split: "(\<Sum>b < 2 ^ length (a # p). eq_pi (a # p) b * eq_pi (c # q) b)
        = (\<Sum>b < 2 ^ length p. eq_pi (a # p) b * eq_pi (c # q) b)
          + (\<Sum>b < 2 ^ length p. eq_pi (a # p) (b + 2 ^ length p) * eq_pi (c # q) (b + 2 ^ length p))"
  proof -
    have decomp: "{..< (2 :: nat) ^ Suc (length p)}
          = {..< 2 ^ length p} \<union> (\<lambda>i. i + 2 ^ length p) ` {..< 2 ^ length p}"
    proof
      show "{..< (2 :: nat) ^ Suc (length p)}
            \<subseteq> {..< 2 ^ length p} \<union> (\<lambda>i. i + 2 ^ length p) ` {..< 2 ^ length p}"
      proof
        fix v assume "v \<in> {..< (2 :: nat) ^ Suc (length p)}"
        then have "v < 2 * 2 ^ length p" by simp
        then show "v \<in> {..< 2 ^ length p} \<union> (\<lambda>i. i + 2 ^ length p) ` {..< 2 ^ length p}"
        proof (cases "v < 2 ^ length p")
          case False
          then have "v - 2 ^ length p < 2 ^ length p" and "v = (v - 2 ^ length p) + 2 ^ length p"
            using \<open>v < 2 * 2 ^ length p\<close> by simp_all
          then show ?thesis by force
        qed simp
      qed
    next
      show "{..< 2 ^ length p} \<union> (\<lambda>i. i + 2 ^ length p) ` {..< 2 ^ length p}
            \<subseteq> {..< (2 :: nat) ^ Suc (length p)}" by auto
    qed
    have inj: "inj_on (\<lambda>i. i + (2 :: nat) ^ length p) {..< 2 ^ length p}"
      by (simp add: inj_on_def)
    have disj: "{..< (2 :: nat) ^ length p} \<inter> (\<lambda>i. i + 2 ^ length p) ` {..< 2 ^ length p} = {}"
      by auto
    have "(\<Sum>b < 2 ^ length (a # p). eq_pi (a # p) b * eq_pi (c # q) b)
          = (\<Sum>b \<in> {..< 2 ^ length p} \<union> (\<lambda>i. i + 2 ^ length p) ` {..< 2 ^ length p}.
               eq_pi (a # p) b * eq_pi (c # q) b)"
      by (simp only: length_Cons decomp)
    also have "\<dots> = (\<Sum>b < 2 ^ length p. eq_pi (a # p) b * eq_pi (c # q) b)
                    + (\<Sum>b \<in> (\<lambda>i. i + 2 ^ length p) ` {..< 2 ^ length p}.
                         eq_pi (a # p) b * eq_pi (c # q) b)"
      by (rule sum.union_disjoint) (use disj in simp_all)
    also have "(\<Sum>b \<in> (\<lambda>i. i + 2 ^ length p) ` {..< 2 ^ length p}.
                  eq_pi (a # p) b * eq_pi (c # q) b)
          = (\<Sum>b < 2 ^ length p.
               eq_pi (a # p) (b + 2 ^ length p) * eq_pi (c # q) (b + 2 ^ length p))"
      by (subst sum.reindex[OF inj]) (simp add: o_def)
    finally show ?thesis .
  qed
  have lo: "(\<Sum>b < 2 ^ length p. eq_pi (a # p) b * eq_pi (c # q) b)
        = (1 - a) * (1 - c) * (\<Sum>b < 2 ^ length p. eq_pi p b * eq_pi q b)"
  proof -
    have "(\<Sum>b < 2 ^ length p. eq_pi (a # p) b * eq_pi (c # q) b)
          = (\<Sum>b < 2 ^ length p. ((1 - a) * (1 - c)) * (eq_pi p b * eq_pi q b))"
      by (intro sum.cong refl) (simp add: eq_pi_cons_lo lpq algebra_simps)
    then show ?thesis
      by (simp add: sum_distrib_left algebra_simps)
  qed
  have hi: "(\<Sum>b < 2 ^ length p. eq_pi (a # p) (b + 2 ^ length p) * eq_pi (c # q) (b + 2 ^ length p))
        = a * c * (\<Sum>b < 2 ^ length p. eq_pi p b * eq_pi q b)"
  proof -
    have "(\<Sum>b < 2 ^ length p. eq_pi (a # p) (b + 2 ^ length p) * eq_pi (c # q) (b + 2 ^ length p))
          = (\<Sum>b < 2 ^ length p. (a * c) * (eq_pi p b * eq_pi q b))"
    proof (intro sum.cong refl)
      fix b assume "b \<in> {..< (2 :: nat) ^ length p}"
      then have blt: "b < 2 ^ length p" by simp
      have bltq: "b < 2 ^ length q" using blt lpq by simp
      have e1: "eq_pi (a # p) (b + 2 ^ length p) = a * eq_pi p b"
        by (rule eq_pi_cons_hi[OF blt])
      have e2: "eq_pi (c # q) (b + 2 ^ length p) = c * eq_pi q b"
        using lpq bltq by (simp add: eq_pi_cons_hi)
      show "eq_pi (a # p) (b + 2 ^ length p) * eq_pi (c # q) (b + 2 ^ length p)
            = (a * c) * (eq_pi p b * eq_pi q b)"
        by (simp add: e1 e2 algebra_simps)
    qed
    then show ?thesis
      by (simp add: sum_distrib_left algebra_simps)
  qed
  have prod_step: "(\<Prod>j < length (a # p). (a # p) ! j * (c # q) ! j
                     + (1 - (a # p) ! j) * (1 - (c # q) ! j))
        = (a * c + (1 - a) * (1 - c)) * (\<Prod>j < length p. p ! j * q ! j + (1 - p ! j) * (1 - q ! j))"
    by (simp only: length_Cons prod_lessThan_Suc_shift nth_Cons_0 nth_Cons_Suc)
  show ?case
    unfolding split lo hi Cons.IH prod_step
    by (simp add: algebra_simps)
qed

section \<open>Activation instance (the theorem fires on a concrete layer)\<close>

text \<open>
  A width-4 layer (2 output bits, 2 input bits) assembled from TWO derived
  families plus ONE sparse leftover gate, against the same gates listed in
  a different order in the layer.  Family 1: two blocks of one Lin tap on
  stride-2 progressions.  Family 2: one Mul block on window progressions.
  Sparse: one Pow3 gate.  The repartition holds as a multiset (the lists
  are permutations), so the main theorem applies at every point.
\<close>

definition demo_group1 :: "int gate_group" where
  "demo_group1 =
     \<lparr> grp_count = 2, grp_out = Prog 0 1, grp_in1 = Prog 0 1, grp_in2 = Fixed 3,
       grp_taps = [\<lparr> tap_kind = GLin, tap_out = 1, tap_in1 = 0, tap_in2 = 0, tap_coeff = 3 \<rparr>] \<rparr>"

definition demo_group2 :: "int gate_group" where
  "demo_group2 =
     \<lparr> grp_count = 1, grp_out = Prog 1 1, grp_in1 = Prog 0 2, grp_in2 = Prog 0 2,
       grp_taps = [\<lparr> tap_kind = GMul, tap_out = 0, tap_in1 = 1, tap_in2 = 2, tap_coeff = 1 \<rparr>] \<rparr>"

definition demo_sparse_gate :: "int gate" where
  "demo_sparse_gate = \<lparr> g_kind = GPow3, g_out = 0, g_in1 = 3, g_in2 = 3, g_coeff = 5 \<rparr>"

definition demo_derived :: "int derived_layer" where
  "demo_derived =
     \<lparr> drv_groups = [demo_group1, demo_group2],
       drv_sparse = [demo_sparse_gate],
       drv_cgroups = [\<lparr> cg_count = 2, cg_out = Prog 0 1, cg_vals = [(0, 7)] \<rparr>],
       drv_csparse = [(3, 11)] \<rparr>"

text \<open>The same gates and constants, hand-listed in a shuffled order.\<close>

definition demo_layer_c :: "int layer" where
  "demo_layer_c =
     \<lparr> layer_width_bits = 2,
       layer_gates =
         [ \<lparr> g_kind = GMul,  g_out = 2, g_in1 = 1, g_in2 = 2, g_coeff = 1 \<rparr>,
           \<lparr> g_kind = GLin,  g_out = 1, g_in1 = 0, g_in2 = 0, g_coeff = 3 \<rparr>,
           demo_sparse_gate,
           \<lparr> g_kind = GLin,  g_out = 3, g_in1 = 2, g_in2 = 2, g_coeff = 3 \<rparr> ],
       layer_consts = [(3, 11), (0, 7), (2, 7)] \<rparr>"

lemma demo_expand_gates:
  "expand_gates demo_derived =
     [ \<lparr> g_kind = GLin, g_out = 1, g_in1 = 0, g_in2 = 0, g_coeff = 3 \<rparr>,
       \<lparr> g_kind = GLin, g_out = 3, g_in1 = 2, g_in2 = 2, g_coeff = 3 \<rparr>,
       \<lparr> g_kind = GMul, g_out = 2, g_in1 = 1, g_in2 = 2, g_coeff = 1 \<rparr>,
       demo_sparse_gate ]"
  by (simp add: expand_gates_def demo_derived_def expand_group_def
                demo_group1_def demo_group2_def tap_gate_def upt_rec)

lemma demo_expand_consts:
  "expand_consts demo_derived = [(0, 7), (2, 7), (3, 11)]"
  by (simp add: expand_consts_def demo_derived_def expand_cgroup_def upt_rec)

lemma demo_repartition:
  "mset (expand_gates demo_derived) = mset (layer_gates demo_layer_c)"
  by (simp add: demo_expand_gates demo_layer_c_def add_mset_commute)

lemma demo_repartition_consts:
  "mset (expand_consts demo_derived) = mset (layer_consts demo_layer_c)"
  by (simp add: demo_expand_consts demo_layer_c_def add_mset_commute)

lemma demo_wf_groups:
  "\<forall>G \<in> set (drv_groups demo_derived). wf_group 2 2 G"
  by (simp add: demo_derived_def demo_group1_def demo_group2_def wf_group_def)

lemma demo_wf_cgroups:
  "\<forall>CG \<in> set (drv_cgroups demo_derived). wf_cgroup 2 CG"
  by (simp add: demo_derived_def wf_cgroup_def)

text \<open>The equivalence fires: at EVERY evaluation point (arbitrary field
  lists of the layer's widths) and for EVERY gate kind, the derived
  closed-form oracle of the demo representation equals the table oracle
  of the shuffled layer - and likewise for the constant vector.\<close>

lemma demo_derived_eq_table:
  fixes z x y :: "int list"
  assumes "length z = 2" and "length x = 2" and "length y = 2"
  shows "derived_eval demo_derived k z x y = gates_mle_eval (layer_gates demo_layer_c) k z x y"
  by (rule derived_mle_eq_table[OF demo_repartition])
     (use assms demo_wf_groups in simp_all)

lemma demo_derived_const_eq_table:
  fixes z :: "int list"
  assumes "length z = 2"
  shows "derived_const_eval demo_derived z = consts_mle_eval (layer_consts demo_layer_c) z"
  by (rule derived_const_mle_eq_table[OF demo_repartition_consts])
     (use assms demo_wf_cgroups in simp_all)

text \<open>And against the definitional MLE, at a sample point: sanity that the
  layer's Mul table reads back the gate coefficient on the hypercube (the
  boolean-point agreement of the packed tuple table).\<close>

lemma demo_table3_bool_point:
  "mle (2 + 2 + 2) (table3 2 (filter (\<lambda>g. g_kind g = GMul) (layer_gates demo_layer_c)))
     (bool_point (2 + 2 + 2) ((2 * 2 ^ 2 + 1) * 2 ^ 2 + 2)) = (1 :: int)"
proof -
  have enc_lt: "(2 * 2 ^ 2 + 1) * 2 ^ 2 + 2 < (2 :: nat) ^ (2 + 2 + 2)" by simp
  have "mle (2 + 2 + 2) (table3 2 (filter (\<lambda>g. g_kind g = GMul) (layer_gates demo_layer_c)))
          (bool_point (2 + 2 + 2) ((2 * 2 ^ 2 + 1) * 2 ^ 2 + 2) :: int list)
        = table3 2 (filter (\<lambda>g. g_kind g = GMul) (layer_gates demo_layer_c))
            ((2 * 2 ^ 2 + 1) * 2 ^ 2 + 2)"
    by (rule mle_bool_point[OF enc_lt])
  also have "\<dots> = 1"
    by (simp add: demo_layer_c_def demo_sparse_gate_def table3_def enc3_def)
  finally show ?thesis .
qed

end
