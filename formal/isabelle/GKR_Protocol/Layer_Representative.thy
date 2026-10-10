(*
  Title:   Layer_Representative.thy
  Session: GKR_Protocol (generic layer)

  An ACTUAL mpoly representative for the layer sumcheck instance: the
  multilinear interpolation of the layer integrand over the 2s-variable
  boolean hypercube, built from concrete mpoly constructors (monomials,
  sums, products).

  This discharges the representation premise `layer_poly_repr` of the
  bridge locale gkr_layer_sumcheck in the AFP mpoly instance (gkr_mpoly,
  Sumcheck_Instance): the premise is NOT vacuous - for every layer,
  claim list and below-vector there is a concrete polynomial the
  sumcheck can be run on.  This realises the instantiation work item
  recorded at the gkr_mpoly interpretation and is the model-side
  discharge of the bridge obligation to the implementation: the real prover's
  round polynomials are evaluations of exactly such a representative.

  Degree note: layer_poly_repr's bound parameter is instantiated with
  the representative's own total degree (reflexively dischargeable), so
  the soundness corollary below carries the factor
  `total_degree (table_repr ...)`.  The multilinear construction keeps
  every variable's individual degree at most one, so its total degree
  is at most 2s (each monomial is a product of 2s degree-<=-1 factors);
  the AFP degree measure is TOTAL degree, hence the O(s) factor - the
  design-bound dbnd = 4 form remains available through a
  max-per-variable-degree instance (see the note at
  layer_sumcheck_soundness_deg4).  We do not formalise the 2s bound:
  the reflexive bound suffices for non-vacuity and for consuming the
  soundness theorem.
*)

theory Layer_Representative
  imports Sumcheck_Instance
begin

section \<open>Boolean factor polynomials\<close>

text \<open>\<open>bfac v b\<close>: the degree-one factor \<open>X_v\<close> (bit set) or \<open>1 - X_v\<close>
  (bit clear), as a concrete mpoly.\<close>

definition bfac :: "nat \<Rightarrow> bool \<Rightarrow> 'a::comm_ring_1 mpoly" where
  "bfac v b = (if b then monom (Poly_Mapping.single v 1) 1
               else 1 + monom (Poly_Mapping.single v 1) (- 1))"

lemma insertion_bfac [simp]:
  "insertion f (bfac v b) = (if b then f v else 1 - f v)"
  by (simp add: bfac_def insertion_add)

lemma vars_one: "vars (1 :: 'a::comm_semiring_1 mpoly) \<subseteq> {}"
  using vars_monom_subset[of 0 "1 :: 'a"] by simp

lemma vars_bfac: "vars (bfac v b) \<subseteq> {v}"
proof (cases b)
  case True
  then show ?thesis
    by (simp add: bfac_def vars_monom_single)
next
  case False
  have "vars (1 + monom (Poly_Mapping.single v 1) (- 1) :: 'a mpoly)
        \<subseteq> vars (1 :: 'a mpoly) \<union> vars (monom (Poly_Mapping.single v 1) (- 1 :: 'a))"
    by (rule vars_add)
  also have "\<dots> \<subseteq> {} \<union> {v}"
    using vars_one vars_monom_single[of v 1 "- 1 :: 'a"] by auto
  finally show ?thesis using False by (simp add: bfac_def)
qed

section \<open>Homomorphism helpers\<close>

lemma insertion_sum_family:
  "insertion f (\<Sum>i \<in> A. p i) = (\<Sum>i \<in> A. insertion f (p i))"
  by (induction A rule: infinite_finite_induct) (simp_all add: insertion_add)

lemma insertion_prod_family:
  "insertion f (\<Prod>i \<in> A. p i) = (\<Prod>i \<in> A. insertion f (p i))"
  by (induction A rule: infinite_finite_induct) (simp_all add: insertion_mult)

lemma vars_prod_family:
  "vars (\<Prod>i \<in> A. p i) \<subseteq> (\<Union>i \<in> A. vars (p i))"
proof (induction A rule: infinite_finite_induct)
  case (infinite A)
  then show ?case using vars_one by auto
next
  case empty
  then show ?case using vars_one by auto
next
  case (insert a A)
  have "vars (\<Prod>i \<in> insert a A. p i) \<subseteq> vars (p a) \<union> vars (\<Prod>i \<in> A. p i)"
    using insert.hyps by (simp add: vars_mult)
  with insert.IH show ?case by auto
qed

lemma insertion_monom_const: "insertion f (monom 0 c) = c"
  using insertion_single[of f 0 0 c] by simp

lemma vars_monom_const: "vars (monom 0 c) \<subseteq> {}"
  using vars_monom_subset[of 0 c] by simp

section \<open>The interpolation table polynomial\<close>

text \<open>Bit \<open>j\<close> of the (x, y) pair in the sumcheck variable order:
  variables \<open>0..<s\<close> carry x's bits, \<open>s..<2s\<close> carry y's (\<open>idx_subst\<close>).\<close>

definition bit2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "bit2 s x y j \<longleftrightarrow> (if j < s then bit_at s x j else bit_at s y (j - s))"

lemma the_idx_subst:
  assumes "j < 2 * s"
  shows "the (idx_subst s x y j :: 'a::zero_neq_one option)
         = (if bit2 s x y j then 1 else 0)"
  using assms by (auto simp add: idx_subst_def bit2_def)

definition table_repr :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> 'a) \<Rightarrow> 'a::comm_ring_1 mpoly" where
  "table_repr s g =
     (\<Sum>x < 2 ^ s. \<Sum>y < 2 ^ s.
        monom 0 (g x y) * (\<Prod>j < 2 * s. bfac j (bit2 s x y j)))"

lemma vars_table_repr: "vars (table_repr s g) \<subseteq> set (upt 0 (2 * s))"
proof -
  have term_vars: "vars (monom 0 (g x y) * (\<Prod>j < 2 * s. bfac j (bit2 s x y j)))
                   \<subseteq> set (upt 0 (2 * s))" for x y
  proof -
    have prod_vars: "vars (\<Prod>j < 2 * s. bfac j (bit2 s x y j) :: 'a mpoly)
          \<subseteq> (\<Union>j < 2 * s. vars (bfac j (bit2 s x y j) :: 'a mpoly))"
      by (rule vars_prod_family)
    have "(\<Union>j < 2 * s. vars (bfac j (bit2 s x y j) :: 'a mpoly))
          \<subseteq> set (upt 0 (2 * s))"
    proof (rule UN_least)
      fix j assume "j \<in> {..<2 * s}"
      then show "vars (bfac j (bit2 s x y j) :: 'a mpoly) \<subseteq> set (upt 0 (2 * s))"
        using vars_bfac[of j "bit2 s x y j"] by auto
    qed
    with prod_vars have pv: "vars (\<Prod>j < 2 * s. bfac j (bit2 s x y j) :: 'a mpoly)
          \<subseteq> set (upt 0 (2 * s))" by blast
    have "vars (monom 0 (g x y) * (\<Prod>j < 2 * s. bfac j (bit2 s x y j)))
          \<subseteq> vars (monom 0 (g x y))
            \<union> vars (\<Prod>j < 2 * s. bfac j (bit2 s x y j) :: 'a mpoly)"
      by (rule vars_mult)
    with pv vars_monom_const show ?thesis by blast
  qed
  have "vars (table_repr s g)
        \<subseteq> (\<Union>x \<in> {..<2 ^ s}. vars (\<Sum>y < 2 ^ s.
             monom 0 (g x y) * (\<Prod>j < 2 * s. bfac j (bit2 s x y j))))"
    unfolding table_repr_def by (intro vars_setsum) simp
  also have "\<dots> \<subseteq> set (upt 0 (2 * s))"
  proof (intro UN_least)
    fix x :: nat assume "x \<in> {..<2 ^ s}"
    have "vars (\<Sum>y < 2 ^ s. monom 0 (g x y) * (\<Prod>j < 2 * s. bfac j (bit2 s x y j)))
          \<subseteq> (\<Union>y \<in> {..<2 ^ s}. vars (monom 0 (g x y) * (\<Prod>j < 2 * s. bfac j (bit2 s x y j))))"
      by (intro vars_setsum) simp
    also have "\<dots> \<subseteq> set (upt 0 (2 * s))"
      using term_vars by (intro UN_least)
    finally show "vars (\<Sum>y < 2 ^ s.
        monom 0 (g x y) * (\<Prod>j < 2 * s. bfac j (bit2 s x y j)))
        \<subseteq> set (upt 0 (2 * s))" .
  qed
  finally show ?thesis .
qed

section \<open>Hypercube evaluation: the interpolation property\<close>

lemma prod_bool_indicator:
  fixes n :: nat
  shows "(\<Prod>j < n. if P j then (1 :: 'a::comm_ring_1) else 0)
         = (if \<forall>j < n. P j then 1 else 0)"
  by (induction n) (auto simp add: less_Suc_eq)

lemma bit2_complete:
  assumes x: "x < 2 ^ s" and x': "x' < 2 ^ s"
    and y: "y < 2 ^ s" and y': "y' < 2 ^ s"
    and agree: "\<forall>j < 2 * s. bit2 s x y j = bit2 s x' y' j"
  shows "x = x' \<and> y = y'"
proof
  have "bit_at s x j = bit_at s x' j" if j: "j < s" for j
  proof -
    from j have "j < 2 * s" by linarith
    with agree have "bit2 s x y j = bit2 s x' y' j" by blast
    with j show ?thesis by (simp add: bit2_def)
  qed
  then show "x = x'" using bit_at_complete[OF x x'] by simp
  have "bit_at s y j = bit_at s y' j" if j: "j < s" for j
  proof -
    from j have "s + j < 2 * s" by linarith
    with agree have "bit2 s x y (s + j) = bit2 s x' y' (s + j)" by blast
    then show ?thesis by (simp add: bit2_def)
  qed
  then show "y = y'" using bit_at_complete[OF y y'] by simp
qed

lemma insertion_table_repr:
  fixes g :: "nat \<Rightarrow> nat \<Rightarrow> 'a::comm_ring_1"
  assumes x': "x' < 2 ^ s" and y': "y' < 2 ^ s"
  shows "insertion (the \<circ> idx_subst s x' y') (table_repr s g) = g x' y'"
proof -
  let ?f = "the \<circ> idx_subst s x' y'"
  have kron: "(\<Prod>j < 2 * s. if bit2 s x y j then ?f j else 1 - ?f j)
              = (if x = x' \<and> y = y' then (1 :: 'a) else 0)"
    if x: "x < 2 ^ s" and y: "y < 2 ^ s" for x y
  proof -
    have "(\<Prod>j < 2 * s. if bit2 s x y j then ?f j else 1 - ?f j)
          = (\<Prod>j < 2 * s. if bit2 s x y j = bit2 s x' y' j then (1 :: 'a) else 0)"
      by (intro prod.cong refl) (auto simp add: the_idx_subst)
    also have "\<dots> = (if \<forall>j < 2 * s. bit2 s x y j = bit2 s x' y' j then 1 else 0)"
      by (rule prod_bool_indicator)
    also have "\<dots> = (if x = x' \<and> y = y' then 1 else 0)"
    proof (cases "\<forall>j < 2 * s. bit2 s x y j = bit2 s x' y' j")
      case True
      with bit2_complete[OF x x' y y'] show ?thesis by simp
    next
      case False
      then have "\<not> (x = x' \<and> y = y')" by auto
      with False show ?thesis by simp
    qed
    finally show ?thesis .
  qed
  have inner: "(\<Sum>y < 2 ^ s. g x y * (if x = x' \<and> y = y' then 1 else 0))
               = (if x = x' then g x y' else 0)" for x
  proof (cases "x = x'")
    case True
    have "(\<Sum>y < 2 ^ s. g x y * (if x = x' \<and> y = y' then 1 else 0))
          = (\<Sum>y < 2 ^ s. if y = y' then g x y else 0)"
      by (intro sum.cong refl) (simp add: True)
    also have "\<dots> = g x y'"
      using y' by (simp add: sum.delta')
    finally show ?thesis by (simp add: True)
  next
    case False
    then show ?thesis by simp
  qed
  have "insertion ?f (table_repr s g)
        = (\<Sum>x < 2 ^ s. \<Sum>y < 2 ^ s.
             g x y * (\<Prod>j < 2 * s. if bit2 s x y j then ?f j else 1 - ?f j))"
    unfolding table_repr_def
    by (simp add: insertion_sum_family insertion_mult insertion_prod_family
                  insertion_monom_const)
  also have "\<dots> = (\<Sum>x < 2 ^ s. \<Sum>y < 2 ^ s.
                     g x y * (if x = x' \<and> y = y' then 1 else 0))"
    by (intro sum.cong refl) (simp add: kron)
  also have "\<dots> = (\<Sum>x < 2 ^ s. if x = x' then g x y' else 0)"
    by (intro sum.cong refl inner)
  also have "\<dots> = g x' y'"
    using x' by (simp add: sum.delta')
  finally show ?thesis .
qed

section \<open>Total-degree bounds for the interpolation construction\<close>

text \<open>The AFP degree measure is TOTAL degree; the interpolation is a sum
  of products of \<open>2s\<close> degree-at-most-one factors, so its total degree is
  at most \<open>2s\<close>.  This makes the representation premise dischargeable with
  the width-dependent bound \<open>dbnd = \<lambda>s. 2 * s\<close>.\<close>

text \<open>The degree of a monomial exponent vector, in the raw form the
  \<open>total_degree\<close> representation uses.  (Self-contained: no dependency on
  the power-products theory, whose heavy syntax overloading interferes
  with this theory's notation.)\<close>

abbreviation mdeg :: "(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> nat" where
  "mdeg m \<equiv> sum (lookup m) (keys m)"

lemma total_degree_le_iff:
  "total_degree p \<le> d \<longleftrightarrow> (\<forall>m \<in> keys (mapping_of p). mdeg m \<le> d)"
  by (simp add: total_degree.rep_eq Max_le_iff)

lemma mdeg_plus: "mdeg (a + b) = mdeg a + mdeg b"
proof -
  let ?S = "keys a \<union> keys b"
  have finS: "finite ?S" by simp
  have keys_sub: "keys (a + b) \<subseteq> ?S"
    by (rule Poly_Mapping.keys_add)
  have "mdeg (a + b) = sum (lookup (a + b)) ?S"
    by (rule sum.mono_neutral_left[OF finS keys_sub]) (simp add: in_keys_iff)
  also have "\<dots> = sum (lookup a) ?S + sum (lookup b) ?S"
    by (simp add: lookup_add sum.distrib)
  also have "sum (lookup a) ?S = mdeg a"
    by (rule sum.mono_neutral_right[OF finS Un_upper1]) (simp add: in_keys_iff)
  also have "sum (lookup b) ?S = mdeg b"
    by (rule sum.mono_neutral_right[OF finS Un_upper2]) (simp add: in_keys_iff)
  finally show ?thesis .
qed

lemma mdeg_le_total_degree:
  assumes "m \<in> keys (mapping_of p)"
  shows "mdeg m \<le> total_degree p"
proof -
  have "mdeg m \<in> insert 0 (mdeg ` keys (mapping_of p))"
    using assms by simp
  then have "mdeg m \<le> Max (insert 0 (mdeg ` keys (mapping_of p)))"
    by (intro Max_ge) simp
  then show ?thesis
    by (simp add: total_degree.rep_eq)
qed

lemma total_degree_mult_le:
  fixes p q :: "'a::comm_semiring_0 mpoly"
  shows "total_degree (p * q) \<le> total_degree p + total_degree q"
proof (subst total_degree_le_iff, intro ballI)
  fix m assume "m \<in> keys (mapping_of (p * q))"
  then have "m \<in> keys (mapping_of p * mapping_of q)"
    by (simp add: times_mpoly.rep_eq)
  then obtain a b where m: "m = a + b"
    and a: "a \<in> keys (mapping_of p)" and b: "b \<in> keys (mapping_of q)"
    using keys_mult by blast
  have "mdeg m = mdeg a + mdeg b"
    by (simp add: m mdeg_plus)
  also have "\<dots> \<le> total_degree p + total_degree q"
    using mdeg_le_total_degree[OF a] mdeg_le_total_degree[OF b]
    by (rule add_mono)
  finally show "mdeg m \<le> total_degree p + total_degree q" .
qed

lemma total_degree_monom_le: "total_degree (monom m a) \<le> mdeg m"
proof (subst total_degree_le_iff, intro ballI)
  fix m' assume "m' \<in> keys (mapping_of (monom m a))"
  then have "m' = m"
    by (simp add: monom.rep_eq split: if_splits)
  then show "mdeg m' \<le> mdeg m"
    by simp
qed

lemma mdeg_single: "mdeg (Poly_Mapping.single v (Suc 0)) = 1"
  by simp

lemma total_degree_bfac_le: "total_degree (bfac v b :: 'a::comm_ring_1 mpoly) \<le> 1"
proof (cases b)
  case True
  then show ?thesis
    using total_degree_monom_le[of "Poly_Mapping.single v 1" "1 :: 'a"]
    by (simp add: bfac_def)
next
  case False
  have "total_degree (1 + monom (Poly_Mapping.single v 1) (- 1) :: 'a mpoly)
        \<le> max (total_degree (1 :: 'a mpoly))
              (total_degree (monom (Poly_Mapping.single v 1) (- 1 :: 'a)))"
    by (rule deg_add)
  also have "\<dots> \<le> 1"
    using total_degree_monom_le[of "Poly_Mapping.single v 1" "- 1 :: 'a"]
    by simp
  finally show ?thesis using False by (simp add: bfac_def)
qed

lemma total_degree_prod_le:
  fixes p :: "'i \<Rightarrow> 'a::comm_semiring_1 mpoly"
  shows "total_degree (\<Prod>i \<in> A. p i) \<le> (\<Sum>i \<in> A. total_degree (p i))"
proof (induction A rule: infinite_finite_induct)
  case (insert a A)
  have "total_degree (\<Prod>i \<in> insert a A. p i)
        \<le> total_degree (p a) + total_degree (\<Prod>i \<in> A. p i)"
    using insert.hyps by (simp add: total_degree_mult_le)
  also have "\<dots> \<le> total_degree (p a) + (\<Sum>i \<in> A. total_degree (p i))"
    using insert.IH by (rule add_left_mono)
  finally show ?case using insert.hyps by simp
qed simp_all

lemma total_degree_sum_le:
  fixes p :: "'i \<Rightarrow> 'a::comm_monoid_add mpoly"
  assumes "\<And>i. i \<in> A \<Longrightarrow> total_degree (p i) \<le> d"
  shows "total_degree (\<Sum>i \<in> A. p i) \<le> d"
  using assms
proof (induction A rule: infinite_finite_induct)
  case (insert a A)
  have "total_degree (\<Sum>i \<in> insert a A. p i)
        \<le> max (total_degree (p a)) (total_degree (\<Sum>i \<in> A. p i))"
    using insert.hyps by (simp add: deg_add)
  also have "\<dots> \<le> d"
    using insert.prems insert.IH by simp
  finally show ?case .
qed (simp_all add: total_degree_zero)

lemma total_degree_table_repr: "total_degree (table_repr s g) \<le> 2 * s"
proof -
  have term_bound: "total_degree
          (monom 0 (g x y) * (\<Prod>j < 2 * s. bfac j (bit2 s x y j))) \<le> 2 * s"
    for x y
  proof (subst total_degree_le_iff, intro ballI)
      \<comment> \<open>every standalone occurrence of the product below carries a type
         annotation: an unanchored occurrence would be inferred at a
         FRESH type variable (the type-binding pathology this corpus
         guards against), making it a different term from the chained
         facts\<close>
    fix m
    assume "m \<in> keys (mapping_of
              (monom 0 (g x y) * (\<Prod>j < 2 * s. bfac j (bit2 s x y j))))"
    then have "m \<in> keys (mapping_of (monom 0 (g x y))
                         * mapping_of (\<Prod>j < 2 * s. bfac j (bit2 s x y j) :: 'a mpoly))"
      by (simp add: times_mpoly.rep_eq)
    then have "m \<in> {a + b |a b.
                     a \<in> keys (mapping_of (monom 0 (g x y)))
                     \<and> b \<in> keys (mapping_of (\<Prod>j < 2 * s. bfac j (bit2 s x y j) :: 'a mpoly))}"
      by (rule subsetD[OF keys_mult])
    then obtain a b where m: "m = a + b"
      and a: "a \<in> keys (mapping_of (monom 0 (g x y)))"
      and b: "b \<in> keys (mapping_of (\<Prod>j < 2 * s. bfac j (bit2 s x y j) :: 'a mpoly))"
      by blast
    from a have a0: "a = 0"
      by (simp add: monom.rep_eq split: if_splits)
    have "mdeg b \<le> total_degree (\<Prod>j < 2 * s. bfac j (bit2 s x y j) :: 'a mpoly)"
      by (rule mdeg_le_total_degree[OF b])
    also have "\<dots> \<le> (\<Sum>j < 2 * s. total_degree (bfac j (bit2 s x y j) :: 'a mpoly))"
      by (rule total_degree_prod_le)
    also have "\<dots> \<le> (\<Sum>j \<in> {..<2 * s}. 1)"
      by (intro sum_mono total_degree_bfac_le)
    finally have "mdeg b \<le> 2 * s" by simp
    then show "mdeg m \<le> 2 * s"
      by (simp add: m a0 mdeg_plus)
  qed
  show ?thesis
    unfolding table_repr_def
    by (intro total_degree_sum_le term_bound)
qed

section \<open>Discharging the representation premise (non-vacuity, bridge to the concrete verifier)\<close>

text \<open>Every layer sumcheck instance has an actual mpoly representative:
  the interpolation of its integrand, with the width-dependent degree
  bound \<open>2s\<close> - exactly the \<open>dbnd = \<lambda>s. 2 * s\<close> function the assembly
  soundness theorems consume in this instance.\<close>

theorem layer_repr_mpoly:
  fixes L :: "'a::{finite, field} layer"
  shows "gkr_mpoly.layer_poly_repr
           (table_repr s (layer_integrand L s claims below))
           L s claims below (2 * s)"
  unfolding gkr_mpoly.layer_poly_repr_def
  by (intro conjI vars_table_repr total_degree_table_repr)
     (simp add: insertion_table_repr)

text \<open>The B2 soundness theorem is consumable with this witness: binding
  the soundness theorem against the interpolation representative yields
  the per-layer bound \<open>2s \<cdot> 2s / |F|\<close> with every representation premise
  discharged - the premise chain is inhabited end to end.  (Stated as a
  fact binding: the sumcheck predicate is a locale constant of the AFP
  development, so the specialised statement lives in the instance's
  terms rather than a fresh top-level formula.)\<close>

lemmas layer_sumcheck_soundness_via_mpoly =
  gkr_mpoly.layer_sumcheck_soundness[OF layer_repr_mpoly]

end
