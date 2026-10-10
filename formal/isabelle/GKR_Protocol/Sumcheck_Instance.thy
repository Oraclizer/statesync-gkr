(*
  Title:   Sumcheck_Instance.thy
  Session: GKR_Protocol (generic layer - no SMT / workload assumptions)

  The per-layer sumcheck instance of the GKR reduction: the layer hypercube
  identity (Theorem B, layer B1) and its correspondence with the AFP entry
  Sumcheck_Protocol (Garvia, Sprenger, Bootle 2024) (Theorem B, layer B2).

  # Layer B1 - the hypercube identity (crate `ssgkr-protocol`, reduce.rs)

  For a layer L with incoming claims [(z_k, c_k)] and the layer-below value
  vector `below` (2^s wires), the module documentation of reduce.rs fixes

    P(x,y) = sum_k c_k [ lin~(z_k,x) V(x) beta(y)
                       + mul~(z_k,x,y) V(x) V(y)
                       + pow3~(z_k,x) V(x)^3 beta(y) ]

  and the identity  sum_{(x,y) in cube} P = sum_k c_k (V_i(z_k) - const~(z_k)).
  This file mechanizes exactly that identity (theorem
  layer_hypercube_identity), with the wiring predicates defined DIRECTLY from
  the gate LIST (duplicated gate tuples accumulate,
  mirroring the += loop of evaluate_circuit / the TableWiring oracle).

  Rust refinement map (crate `ssgkr-protocol`):
    lin_wt/mul_wt/pow3_wt   ~ the per-kind coefficient bookings of
                              TableWiring::eval_predicate_mle restricted to
                              boolean (x,y) (gate-list sum with +=)
    lin_mle/mul_mle/pow3_mle~ TableWiring::eval_predicate_mle at a general
                              claim point z and boolean x, y
    const_mle               ~ TableWiring::eval_const_mle
    beta_idx                ~ beta_eval at a boolean point
    layer_integrand         ~ the summand of P(x,y) over the (x,y) cube
    layer_claim_sum         ~ the verifier's claim
                              sum_k c_k (target_k - const~(z_k)) with the
                              TRUE targets target_k = V_i~(z_k)
                              (reduce.rs::verify, `claim`)

  # Layer B2 - AFP correspondence

  The locale gkr_layer_sumcheck places the layer sumcheck on the AFP locale
  multi_variate_polynomial (imported, never re-proved).  The connection is
  packaged as the DEFINITION layer_poly_repr (no locale axioms are added, so
  there are no orphan assumptions): a polynomial p represents the layer
  instance iff its variables live in {0..<2s}, its AFP degree is bounded,
  and it agrees with the layer integrand on the boolean hypercube.  The AFP
  theorems soundness_inductive / completeness_inductive are then consumed
  per layer (layer_sumcheck_soundness / layer_sumcheck_completeness).

  Degree-bound note: the AFP `deg` is an abstract operation; its concrete
  AFP instantiation is the TOTAL degree of an mpoly.  The per-round
  univariate degree bound of the Rust verifier (LAYER_ROUND_DEGREE = 4,
  reduce.rs) corresponds to a max-per-variable degree measure, which also
  satisfies all locale axioms but is NOT the AFP-shipped instance.  To keep
  every assumption dischargeable in SOME instance (no orphan assumptions),
  layer_poly_repr carries the degree bound as a parameter `dbnd`; the
  d = 4 specialisation (matching LAYER_ROUND_DEGREE) is stated separately.

  # Probability model

  Interactive public-coin, identical to the AFP model: challenges are drawn
  uniformly from a finite field type 'a (pmf_of_set over tuples).  The
  Fiat-Shamir transformation (Rust `Transcript`) is OUTSIDE this model: its
  soundness is a blackbox assumption on the challenger implementation
  (design section B.3), standard ROM practice.  Nothing in this file models
  the transcript.
*)

theory Sumcheck_Instance
  imports
    Layered_Circuit
    Multilinear_Extension
    "Sumcheck_Protocol.Completeness_Proof"
    "Sumcheck_Protocol.Soundness_Proof"
    "Sumcheck_Protocol.Concrete_Multivariate_Polynomials"
begin

section \<open>Per-kind wiring weight tables (gate-list semantics)\<close>

text \<open>
  The coefficient booked by a gate list for one (kind, out, in-wire) cell.
  Duplicated tuples accumulate (list semantics): this is the boolean-point
  restriction of the Rust wiring oracle, where TableWiring sums
  \<open>coeff * eq(z,out) * eq(x,in1) [* eq(y,in2)]\<close> over the gate list.
\<close>

definition lin_wt :: "'f::comm_ring_1 gate list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f" where
  "lin_wt gs z x =
     sum_list (map g_coeff
       (filter (\<lambda>g. g_kind g = GLin \<and> g_out g = z \<and> g_in1 g = x) gs))"

definition mul_wt :: "'f::comm_ring_1 gate list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f" where
  "mul_wt gs z x y =
     sum_list (map g_coeff
       (filter (\<lambda>g. g_kind g = GMul \<and> g_out g = z \<and> g_in1 g = x \<and> g_in2 g = y) gs))"

definition pow3_wt :: "'f::comm_ring_1 gate list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f" where
  "pow3_wt gs z x =
     sum_list (map g_coeff
       (filter (\<lambda>g. g_kind g = GPow3 \<and> g_out g = z \<and> g_in1 g = x) gs))"

section \<open>Splitting a layer's gate sum by kind\<close>

text \<open>
  The wire-z gate contribution sum of @{const layer_eval}, regrouped into
  the three per-kind weight tables.  This is the boolean-point core of the
  layer identity: each gate's contribution is recovered by a Kronecker
  selection over the input cube.
\<close>

lemma gate_sum_kind_split:
  fixes gs :: "'f::comm_ring_1 gate list" and below :: "'f list" and z :: nat
  assumes "\<forall>g \<in> set gs. g_in1 g < 2 ^ s \<and> g_in2 g < 2 ^ s"
  shows "sum_list (map (\<lambda>g. gate_contrib g below) (filter (\<lambda>g. g_out g = z) gs))
       = (\<Sum>x<2^s. lin_wt gs z x * below ! x)
       + (\<Sum>x<2^s. \<Sum>y<2^s. mul_wt gs z x y * (below ! x * below ! y))
       + (\<Sum>x<2^s. pow3_wt gs z x * (below ! x * below ! x * below ! x))"
  using assms
proof (induction gs)
  case Nil
  show ?case by (simp add: lin_wt_def mul_wt_def pow3_wt_def)
next
  case (Cons g gs)
  have in_range: "\<forall>g' \<in> set gs. g_in1 g' < 2 ^ s \<and> g_in2 g' < 2 ^ s"
    using Cons.prems by simp
  have in1: "g_in1 g < 2 ^ s" and in2: "g_in2 g < 2 ^ s"
    using Cons.prems by simp_all
  note IH = Cons.IH[OF in_range]
  show ?case
  proof (cases "g_out g = z")
    case False
    then show ?thesis using IH
      by (simp add: lin_wt_def mul_wt_def pow3_wt_def)
  next
    case True
    show ?thesis
    proof (cases "g_kind g")
      case GLin
      have lw: "\<And>x. lin_wt (g # gs) z x =
                  (if g_in1 g = x then g_coeff g else 0) + lin_wt gs z x"
        using True GLin by (simp add: lin_wt_def)
      have mw: "\<And>x y. mul_wt (g # gs) z x y = mul_wt gs z x y"
        using GLin by (simp add: mul_wt_def)
      have pw: "\<And>x. pow3_wt (g # gs) z x = pow3_wt gs z x"
        using GLin by (simp add: pow3_wt_def)
      have delta: "(\<Sum>x<2^s. (if g_in1 g = x then g_coeff g else 0) * below ! x)
                 = g_coeff g * below ! (g_in1 g)"
      proof -
        have "(\<Sum>x<2^s. (if g_in1 g = x then g_coeff g else 0) * below ! x)
            = (\<Sum>x<2^s. (if g_in1 g = x then g_coeff g * below ! x else 0))"
          by (intro sum.cong refl) simp
        also have "\<dots> = g_coeff g * below ! (g_in1 g)"
          using in1 by (simp add: sum.delta')
        finally show ?thesis .
      qed
      have "(\<Sum>x<2^s. lin_wt (g # gs) z x * below ! x)
          = g_coeff g * below ! (g_in1 g) + (\<Sum>x<2^s. lin_wt gs z x * below ! x)"
        by (simp add: lw distrib_right sum.distrib delta)
      then show ?thesis using True GLin IH
        by (simp add: mw pw gate_contrib_def algebra_simps)
    next
      case GMul
      have lw: "\<And>x. lin_wt (g # gs) z x = lin_wt gs z x"
        using GMul by (simp add: lin_wt_def)
      have mw: "\<And>x y. mul_wt (g # gs) z x y =
                  (if g_in1 g = x \<and> g_in2 g = y then g_coeff g else 0) + mul_wt gs z x y"
        using True GMul by (simp add: mul_wt_def)
      have pw: "\<And>x. pow3_wt (g # gs) z x = pow3_wt gs z x"
        using GMul by (simp add: pow3_wt_def)
      have inner: "\<And>x. (\<Sum>y<2^s.
              (if g_in1 g = x \<and> g_in2 g = y then g_coeff g else 0) * (below ! x * below ! y))
            = (if g_in1 g = x then g_coeff g * (below ! x * below ! (g_in2 g)) else 0)"
      proof -
        fix x
        show "(\<Sum>y<2^s.
              (if g_in1 g = x \<and> g_in2 g = y then g_coeff g else 0) * (below ! x * below ! y))
            = (if g_in1 g = x then g_coeff g * (below ! x * below ! (g_in2 g)) else 0)"
        proof (cases "g_in1 g = x")
          case True
          have "(\<Sum>y<2^s. (if g_in2 g = y then g_coeff g else 0) * (below ! x * below ! y))
              = (\<Sum>y<2^s. (if g_in2 g = y then g_coeff g * (below ! x * below ! y) else 0))"
            by (intro sum.cong refl) simp
          also have "\<dots> = g_coeff g * (below ! x * below ! (g_in2 g))"
            using in2 by (simp add: sum.delta')
          finally show ?thesis using True by simp
        next
          case False
          then show ?thesis by simp
        qed
      qed
      have delta2: "(\<Sum>x<2^s. \<Sum>y<2^s.
              (if g_in1 g = x \<and> g_in2 g = y then g_coeff g else 0) * (below ! x * below ! y))
            = g_coeff g * (below ! (g_in1 g) * below ! (g_in2 g))"
        using in1 by (simp add: inner sum.delta')
      have "(\<Sum>x<2^s. \<Sum>y<2^s. mul_wt (g # gs) z x y * (below ! x * below ! y))
          = g_coeff g * (below ! (g_in1 g) * below ! (g_in2 g))
          + (\<Sum>x<2^s. \<Sum>y<2^s. mul_wt gs z x y * (below ! x * below ! y))"
        by (simp add: mw distrib_right sum.distrib delta2)
      then show ?thesis using True GMul IH
        by (simp add: lw pw gate_contrib_def algebra_simps)
    next
      case GPow3
      have lw: "\<And>x. lin_wt (g # gs) z x = lin_wt gs z x"
        using GPow3 by (simp add: lin_wt_def)
      have mw: "\<And>x y. mul_wt (g # gs) z x y = mul_wt gs z x y"
        using GPow3 by (simp add: mul_wt_def)
      have pw: "\<And>x. pow3_wt (g # gs) z x =
                  (if g_in1 g = x then g_coeff g else 0) + pow3_wt gs z x"
        using True GPow3 by (simp add: pow3_wt_def)
      have delta: "(\<Sum>x<2^s. (if g_in1 g = x then g_coeff g else 0)
                             * (below ! x * below ! x * below ! x))
                 = g_coeff g * (below ! (g_in1 g) * below ! (g_in1 g) * below ! (g_in1 g))"
      proof -
        have "(\<Sum>x<2^s. (if g_in1 g = x then g_coeff g else 0)
                        * (below ! x * below ! x * below ! x))
            = (\<Sum>x<2^s. (if g_in1 g = x
                          then g_coeff g * (below ! x * below ! x * below ! x) else 0))"
          by (intro sum.cong refl) simp
        also have "\<dots> = g_coeff g * (below ! (g_in1 g) * below ! (g_in1 g) * below ! (g_in1 g))"
          using in1 by (simp add: sum.delta')
        finally show ?thesis .
      qed
      have "(\<Sum>x<2^s. pow3_wt (g # gs) z x * (below ! x * below ! x * below ! x))
          = g_coeff g * (below ! (g_in1 g) * below ! (g_in1 g) * below ! (g_in1 g))
          + (\<Sum>x<2^s. pow3_wt gs z x * (below ! x * below ! x * below ! x))"
        by (simp add: pw distrib_right sum.distrib delta)
      then show ?thesis using True GPow3 IH
        by (simp add: lw mw gate_contrib_def algebra_simps)
    qed
  qed
qed

section \<open>Claim-point lifting of the weight tables\<close>

text \<open>
  Multilinear extension in the OUTPUT-wire coordinate only: the claim point
  \<open>zpt\<close> is a general field point, the input wires x (and y) stay boolean
  indices.  Unfolding @{const mle}, \<open>lin_mle L zpt x =
  sum over Lin gates with in1 = x of coeff * eq_pi zpt (out)\<close>, which is
  exactly \<open>TableWiring::eval_predicate_mle\<close> at boolean x (where
  \<open>eq(x, in1)\<close> is the Kronecker delta).  Same for mul (boolean x, y) and
  pow3; \<open>const_mle\<close> is \<open>eval_const_mle\<close> verbatim.
\<close>

definition lin_mle :: "'f::comm_ring_1 layer \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f" where
  "lin_mle L zpt x = mle (layer_width_bits L) (\<lambda>z. lin_wt (layer_gates L) z x) zpt"

definition mul_mle :: "'f::comm_ring_1 layer \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f" where
  "mul_mle L zpt x y = mle (layer_width_bits L) (\<lambda>z. mul_wt (layer_gates L) z x y) zpt"

definition pow3_mle :: "'f::comm_ring_1 layer \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f" where
  "pow3_mle L zpt x = mle (layer_width_bits L) (\<lambda>z. pow3_wt (layer_gates L) z x) zpt"

definition const_mle :: "'f::comm_ring_1 layer \<Rightarrow> 'f list \<Rightarrow> 'f" where
  "const_mle L zpt = mle (layer_width_bits L) (const_at L) zpt"

text \<open>
  The layer-value MLE, split along the three gate kinds.  Instantiating
  \<open>zpt\<close> with a boolean point recovers the native layer identity of
  \<open>Layered_Circuit\<close>; at a general point it is the wiring identity
  \<open>V_i~(z) = const~(z) + sum_x lin~ V + sum_xy mul~ V V + sum_x pow3~ V^3\<close>
  of the reduce.rs module documentation.
\<close>

lemma layer_value_mle_split:
  fixes L :: "'f::comm_ring_1 layer" and below :: "'f list"
  assumes gates_in: "\<forall>g \<in> set (layer_gates L). g_in1 g < 2 ^ s \<and> g_in2 g < 2 ^ s"
  shows "mle (layer_width_bits L) ((!) (layer_eval L below)) zpt
       = const_mle L zpt
       + ((\<Sum>x<2^s. lin_mle L zpt x * below ! x)
       + (\<Sum>x<2^s. \<Sum>y<2^s. mul_mle L zpt x y * (below ! x * below ! y))
       + (\<Sum>x<2^s. pow3_mle L zpt x * (below ! x * below ! x * below ! x)))"
proof -
  let ?n = "layer_width_bits L"
  let ?A = "\<lambda>z. (\<Sum>x<2^s. lin_wt (layer_gates L) z x * below ! x)"
  let ?B = "\<lambda>z. (\<Sum>x<2^s. \<Sum>y<2^s. mul_wt (layer_gates L) z x y * (below ! x * below ! y))"
  let ?C = "\<lambda>z. (\<Sum>x<2^s. pow3_wt (layer_gates L) z x * (below ! x * below ! x * below ! x))"

  have nth_eval: "\<And>z. z < 2 ^ ?n \<Longrightarrow>
      layer_eval L below ! z = const_at L z + (?A z + ?B z + ?C z)"
  proof -
    fix z :: nat assume "z < 2 ^ ?n"
    then have "z < layer_width L" by (simp add: layer_width_def)
    then show "layer_eval L below ! z = const_at L z + (?A z + ?B z + ?C z)"
      using gate_sum_kind_split[OF gates_in]
      by (simp add: layer_eval_nth add.assoc)
  qed

  have "mle ?n ((!) (layer_eval L below)) zpt
      = (\<Sum>z<2^?n. eq_pi zpt z * (const_at L z + (?A z + ?B z + ?C z)))"
    unfolding mle_def by (intro sum.cong refl) (simp add: nth_eval)
  also have "\<dots> = (\<Sum>z<2^?n. eq_pi zpt z * const_at L z)
                + ((\<Sum>z<2^?n. eq_pi zpt z * ?A z)
                + (\<Sum>z<2^?n. eq_pi zpt z * ?B z)
                + (\<Sum>z<2^?n. eq_pi zpt z * ?C z))"
    by (simp add: distrib_left sum.distrib)
  also have "(\<Sum>z<2^?n. eq_pi zpt z * const_at L z) = const_mle L zpt"
    by (simp add: const_mle_def mle_def)
  also have "(\<Sum>z<2^?n. eq_pi zpt z * ?A z)
           = (\<Sum>x<2^s. lin_mle L zpt x * below ! x)"
  proof -
    have "(\<Sum>z<2^?n. eq_pi zpt z * ?A z)
        = (\<Sum>z<2^?n. \<Sum>x<2^s. eq_pi zpt z * lin_wt (layer_gates L) z x * below ! x)"
      by (simp add: sum_distrib_left mult.assoc)
    also have "\<dots> = (\<Sum>x<2^s. \<Sum>z<2^?n. eq_pi zpt z * lin_wt (layer_gates L) z x * below ! x)"
      by (rule sum.swap)
    also have "\<dots> = (\<Sum>x<2^s. (\<Sum>z<2^?n. eq_pi zpt z * lin_wt (layer_gates L) z x) * below ! x)"
      by (simp add: sum_distrib_right)
    also have "\<dots> = (\<Sum>x<2^s. lin_mle L zpt x * below ! x)"
      by (simp add: lin_mle_def mle_def)
    finally show ?thesis .
  qed
  also have "(\<Sum>z<2^?n. eq_pi zpt z * ?B z)
           = (\<Sum>x<2^s. \<Sum>y<2^s. mul_mle L zpt x y * (below ! x * below ! y))"
  proof -
    have "(\<Sum>z<2^?n. eq_pi zpt z * ?B z)
        = (\<Sum>z<2^?n. \<Sum>x<2^s. \<Sum>y<2^s.
             eq_pi zpt z * mul_wt (layer_gates L) z x y * (below ! x * below ! y))"
      by (simp add: sum_distrib_left mult.assoc)
    also have "\<dots> = (\<Sum>x<2^s. \<Sum>z<2^?n. \<Sum>y<2^s.
             eq_pi zpt z * mul_wt (layer_gates L) z x y * (below ! x * below ! y))"
      by (rule sum.swap)
    also have "\<dots> = (\<Sum>x<2^s. \<Sum>y<2^s. \<Sum>z<2^?n.
             eq_pi zpt z * mul_wt (layer_gates L) z x y * (below ! x * below ! y))"
      by (intro sum.cong refl sum.swap)
    also have "\<dots> = (\<Sum>x<2^s. \<Sum>y<2^s.
             (\<Sum>z<2^?n. eq_pi zpt z * mul_wt (layer_gates L) z x y) * (below ! x * below ! y))"
      by (simp add: sum_distrib_right)
    also have "\<dots> = (\<Sum>x<2^s. \<Sum>y<2^s. mul_mle L zpt x y * (below ! x * below ! y))"
      by (simp add: mul_mle_def mle_def)
    finally show ?thesis .
  qed
  also have "(\<Sum>z<2^?n. eq_pi zpt z * ?C z)
           = (\<Sum>x<2^s. pow3_mle L zpt x * (below ! x * below ! x * below ! x))"
  proof -
    have "(\<Sum>z<2^?n. eq_pi zpt z * ?C z)
        = (\<Sum>z<2^?n. \<Sum>x<2^s.
             eq_pi zpt z * pow3_wt (layer_gates L) z x * (below ! x * below ! x * below ! x))"
      by (simp add: sum_distrib_left mult.assoc)
    also have "\<dots> = (\<Sum>x<2^s. \<Sum>z<2^?n.
             eq_pi zpt z * pow3_wt (layer_gates L) z x * (below ! x * below ! x * below ! x))"
      by (rule sum.swap)
    also have "\<dots> = (\<Sum>x<2^s.
             (\<Sum>z<2^?n. eq_pi zpt z * pow3_wt (layer_gates L) z x)
             * (below ! x * below ! x * below ! x))"
      by (simp add: sum_distrib_right)
    also have "\<dots> = (\<Sum>x<2^s. pow3_mle L zpt x * (below ! x * below ! x * below ! x))"
      by (simp add: pow3_mle_def mle_def)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

section \<open>The layer hypercube identity (B1)\<close>

text \<open>\<open>beta_idx s y\<close> = the all-zero indicator @{const beta} at the boolean
  point of index y (Rust \<open>beta_eval\<close> at a boolean point).  On the cube it
  is the Kronecker delta at 0 and its cube sum is 1, which is what lifts
  the unary (lin/pow3) terms onto the (x, y) hypercube.\<close>

definition beta_idx :: "nat \<Rightarrow> nat \<Rightarrow> 'f::comm_ring_1" where
  "beta_idx s y = beta (bool_point s y)"

lemma beta_idx_delta:
  assumes "y < 2 ^ s"
  shows "beta_idx s y = (if y = 0 then 1 else (0 :: 'f::comm_ring_1))"
  using assms by (simp add: beta_idx_def beta_bool_point)

lemma sum_beta_idx: "(\<Sum>y<2^s. beta_idx s y) = (1 :: 'f::comm_ring_1)"
  by (simp add: beta_idx_def sum_beta_bool_points)

text \<open>The single-claim integrand of the layer sumcheck polynomial P at a
  boolean cube cell (x, y) (reduce.rs module documentation, one claim
  point z with coefficient 1).\<close>

definition layer_integrand1 ::
  "'f::comm_ring_1 layer \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f" where
  "layer_integrand1 L s zpt below x y =
     lin_mle L zpt x * below ! x * beta_idx s y
   + mul_mle L zpt x y * (below ! x * below ! y)
   + pow3_mle L zpt x * (below ! x * below ! x * below ! x) * beta_idx s y"

theorem layer_hypercube_identity1:
  fixes L :: "'f::comm_ring_1 layer"
  assumes gates_in: "\<forall>g \<in> set (layer_gates L). g_in1 g < 2 ^ s \<and> g_in2 g < 2 ^ s"
  shows "(\<Sum>x<2^s. \<Sum>y<2^s. layer_integrand1 L s zpt below x y)
       = mle (layer_width_bits L) ((!) (layer_eval L below)) zpt - const_mle L zpt"
proof -
  have lin_lift: "(\<Sum>x<2^s. \<Sum>y<2^s. lin_mle L zpt x * below ! x * beta_idx s y)
                = (\<Sum>x<2^s. lin_mle L zpt x * below ! x)"
  proof -
    have "(\<Sum>x<2^s. \<Sum>y<2^s. lin_mle L zpt x * below ! x * beta_idx s y)
        = (\<Sum>x<2^s. lin_mle L zpt x * below ! x * (\<Sum>y<2^s. beta_idx s y))"
      by (simp add: sum_distrib_left)
    then show ?thesis by (simp add: sum_beta_idx)
  qed
  have pow3_lift: "(\<Sum>x<2^s. \<Sum>y<2^s.
          pow3_mle L zpt x * (below ! x * below ! x * below ! x) * beta_idx s y)
        = (\<Sum>x<2^s. pow3_mle L zpt x * (below ! x * below ! x * below ! x))"
  proof -
    have "(\<Sum>x<2^s. \<Sum>y<2^s.
            pow3_mle L zpt x * (below ! x * below ! x * below ! x) * beta_idx s y)
        = (\<Sum>x<2^s. pow3_mle L zpt x * (below ! x * below ! x * below ! x)
                    * (\<Sum>y<2^s. beta_idx s y))"
      by (simp add: sum_distrib_left)
    then show ?thesis by (simp add: sum_beta_idx)
  qed
  have "(\<Sum>x<2^s. \<Sum>y<2^s. layer_integrand1 L s zpt below x y)
      = (\<Sum>x<2^s. \<Sum>y<2^s. lin_mle L zpt x * below ! x * beta_idx s y)
      + ((\<Sum>x<2^s. \<Sum>y<2^s. mul_mle L zpt x y * (below ! x * below ! y))
      + (\<Sum>x<2^s. \<Sum>y<2^s.
           pow3_mle L zpt x * (below ! x * below ! x * below ! x) * beta_idx s y))"
    by (simp add: layer_integrand1_def sum.distrib add.assoc)
  also have "\<dots> = (\<Sum>x<2^s. lin_mle L zpt x * below ! x)
      + ((\<Sum>x<2^s. \<Sum>y<2^s. mul_mle L zpt x y * (below ! x * below ! y))
      + (\<Sum>x<2^s. pow3_mle L zpt x * (below ! x * below ! x * below ! x)))"
    by (simp add: lin_lift pow3_lift)
  also have "\<dots> = mle (layer_width_bits L) ((!) (layer_eval L below)) zpt - const_mle L zpt"
    using layer_value_mle_split[OF gates_in]
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

text \<open>Multi-claim combination: incoming claim points with verifier
  coefficients, exactly the shape reduce.rs carries between layers
  (\<open>incoming = [(x*, 1), (y*, r)]\<close> after the first layer).\<close>

definition layer_integrand ::
  "'f::comm_ring_1 layer \<Rightarrow> nat \<Rightarrow> ('f list \<times> 'f) list \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f" where
  "layer_integrand L s claims below x y =
     (\<Sum>(z, c)\<leftarrow>claims. c * layer_integrand1 L s z below x y)"

definition layer_claim_sum ::
  "'f::comm_ring_1 layer \<Rightarrow> ('f list \<times> 'f) list \<Rightarrow> 'f list \<Rightarrow> 'f" where
  "layer_claim_sum L claims below =
     (\<Sum>(z, c)\<leftarrow>claims. c * (mle (layer_width_bits L) ((!) (layer_eval L below)) z
                             - const_mle L z))"

theorem layer_hypercube_identity:
  fixes L :: "'f::comm_ring_1 layer"
  assumes gates_in: "\<forall>g \<in> set (layer_gates L). g_in1 g < 2 ^ s \<and> g_in2 g < 2 ^ s"
  shows "(\<Sum>x<2^s. \<Sum>y<2^s. layer_integrand L s claims below x y)
       = layer_claim_sum L claims below"
proof (induction claims)
  case Nil
  show ?case by (simp add: layer_integrand_def layer_claim_sum_def)
next
  case (Cons zc claims)
  obtain z c where zc: "zc = (z, c)" by (cases zc)
  have "(\<Sum>x<2^s. \<Sum>y<2^s. layer_integrand L s (zc # claims) below x y)
      = (\<Sum>x<2^s. \<Sum>y<2^s.
           c * layer_integrand1 L s z below x y + layer_integrand L s claims below x y)"
    by (simp add: layer_integrand_def zc)
  also have "\<dots> = c * (\<Sum>x<2^s. \<Sum>y<2^s. layer_integrand1 L s z below x y)
                + (\<Sum>x<2^s. \<Sum>y<2^s. layer_integrand L s claims below x y)"
    by (simp add: sum.distrib sum_distrib_left)
  also have "\<dots> = c * (mle (layer_width_bits L) ((!) (layer_eval L below)) z
                       - const_mle L z)
                + layer_claim_sum L claims below"
    by (simp add: layer_hypercube_identity1[OF gates_in] Cons.IH)
  also have "\<dots> = layer_claim_sum L (zc # claims) below"
    by (simp add: layer_claim_sum_def zc)
  finally show ?case .
qed

section \<open>Activation instance (non-vacuity witness for B1)\<close>

text \<open>
  The demo layer of \<open>Layered_Circuit\<close> (all three gate kinds and a constant),
  claim point [3] over the integers, below = [2, 1]:

    layer values     = [2, 2]              (\<open>demo_eval\<close>)
    V~([3])          = (1-3)*2 + 3*2 = 2
    const~([3])      = (1-3)*(-5)   = 10
    rhs              = 2 - 10       = -8

    lhs: lin  x=0: (1-3)*3 * 2 * [y=0] = -12
         mul  x=0,y=1: 3 * (2*1)       =   6
         pow3 x=1: (1-3)*1 * 1 * [y=0] =  -2      total -8.
\<close>

lemma demo_hypercube_identity_value:
  "(\<Sum>x<2^1. \<Sum>y<2^1. layer_integrand1 demo_layer 1 [3] [2, 1] x y) = (- 8 :: int)"
proof -
  have expand: "{..<(2::nat)} = {0, 1}" by auto
  show ?thesis
    unfolding layer_integrand1_def lin_mle_def mul_mle_def pow3_mle_def
              lin_wt_def mul_wt_def pow3_wt_def beta_idx_def
    by (simp add: expand demo_layer_def mle_def eq_pi_def beta_prod
                  bool_point_def bit_at_iff_odd_div upt_rec)
qed

lemma demo_hypercube_identity_rhs:
  "mle (layer_width_bits demo_layer) ((!) (layer_eval demo_layer [2, 1])) [3]
   - const_mle demo_layer [3] = (- 8 :: int)"
proof -
  have expand: "{..<(2::nat)} = {0, 1}" by auto
  have wb: "layer_width_bits demo_layer = 1"
    by (simp add: demo_layer_def)
  have vals: "layer_eval demo_layer [2, 1] = [2, 2]"
    using demo_eval
    by (simp add: circuit_output_def demo_circuit_def Let_def)
  have cvals: "const_at demo_layer 0 = (- 5 :: int)"
              "const_at demo_layer (Suc 0) = (0 :: int)"
    by (simp_all add: const_at_def demo_layer_def)
  show ?thesis
    unfolding const_mle_def
    by (simp add: expand wb vals cvals mle_def eq_pi_def
                  bool_point_def bit_at_iff_odd_div upt_rec)
qed

section \<open>Index/substitution bridge to the AFP protocol (B2 plumbing)\<close>

text \<open>
  The AFP sumcheck sums over substitutions \<open>substs V H\<close>; the layer identity
  sums over cube indices.  This section builds the bijection between
  \<open>substs {0..<2s} {0,1}\<close> and index pairs \<open>{..<2^s} x {..<2^s}\<close>, in the
  frozen variable convention (S-2 / poly.rs): variable 0 is the most
  significant bit, the x block (variables 0..<s) precedes the y block
  (variables s..<2s), matching the Rust binding order x then y.
\<close>

definition bits_idx :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat" where
  "bits_idx b n = (\<Sum>j<n. if b j then 2 ^ (n - 1 - j) else 0)"

lemma sum_lessThan_Suc_shift:
  fixes f :: "nat \<Rightarrow> 'b::comm_monoid_add"
  shows "(\<Sum>j < Suc n. f j) = f 0 + (\<Sum>j < n. f (Suc j))"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  then show ?case by (simp add: add.assoc)
qed

lemma bits_idx_Suc:
  "bits_idx b (Suc n) = (if b 0 then 2 ^ n else 0) + bits_idx (b \<circ> Suc) n"
proof -
  have "bits_idx b (Suc n) = (\<Sum>j<Suc n. if b j then 2 ^ (Suc n - 1 - j) else 0)"
    by (simp add: bits_idx_def)
  also have "\<dots> = (if b 0 then 2 ^ (Suc n - 1 - 0) else 0)
      + (\<Sum>j<n. if b (Suc j) then 2 ^ (Suc n - 1 - Suc j) else 0)"
    by (rule sum_lessThan_Suc_shift)
  also have "(\<Sum>j<n. if b (Suc j) then 2 ^ (Suc n - 1 - Suc j) else (0::nat))
           = (\<Sum>j<n. if b (Suc j) then 2 ^ (n - 1 - j) else 0)"
  proof (intro sum.cong refl)
    fix j assume "j \<in> {..<n}"
    have "Suc n - 1 - Suc j = n - 1 - j" by arith
    then show "(if b (Suc j) then 2 ^ (Suc n - 1 - Suc j) else (0::nat))
             = (if b (Suc j) then 2 ^ (n - 1 - j) else 0)" by simp
  qed
  also have "(if b 0 then 2 ^ (Suc n - 1 - 0) else (0::nat))
      + (\<Sum>j<n. if b (Suc j) then 2 ^ (n - 1 - j) else 0)
      = (if b 0 then 2 ^ n else 0) + bits_idx (b \<circ> Suc) n"
    by (simp add: bits_idx_def o_def)
  finally show ?thesis .
qed

lemma bits_idx_lt: "bits_idx b n < 2 ^ n"
proof (induction n arbitrary: b)
  case 0
  show ?case by (simp add: bits_idx_def)
next
  case (Suc n)
  have "bits_idx (b \<circ> Suc) n < 2 ^ n" by (rule Suc.IH)
  then show ?case by (auto simp add: bits_idx_Suc)
qed

lemma bit_at_bits_idx:
  assumes "j < n"
  shows "bit_at n (bits_idx b n) j = b j"
  using assms
proof (induction n arbitrary: b j)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have lt: "bits_idx (b \<circ> Suc) n < 2 ^ n" by (rule bits_idx_lt)
  show ?case
  proof (cases j)
    case 0
    show ?thesis
    proof (cases "b 0")
      case True
      then have "bits_idx b (Suc n) = bits_idx (b \<circ> Suc) n + 2 ^ n"
        by (simp add: bits_idx_Suc)
      then show ?thesis using 0 True bit_at_head_hi[OF lt] by simp
    next
      case False
      then have "bits_idx b (Suc n) = bits_idx (b \<circ> Suc) n"
        by (simp add: bits_idx_Suc)
      then show ?thesis using 0 False bit_at_head_lo[OF lt] by simp
    qed
  next
    case (Suc k)
    then have kn: "k < n" using Suc.prems by simp
    show ?thesis
    proof (cases "b 0")
      case True
      then have eq: "bits_idx b (Suc n) = bits_idx (b \<circ> Suc) n + 2 ^ n"
        by (simp add: bits_idx_Suc)
      have "bit_at (Suc n) (bits_idx b (Suc n)) (Suc k)
          = bit_at n (bits_idx (b \<circ> Suc) n) k"
        unfolding eq by (rule bit_at_tail_hi[OF lt kn])
      also have "\<dots> = (b \<circ> Suc) k" by (rule Suc.IH[OF kn])
      finally show ?thesis using Suc by simp
    next
      case False
      then have eq: "bits_idx b (Suc n) = bits_idx (b \<circ> Suc) n"
        by (simp add: bits_idx_Suc)
      have "bit_at (Suc n) (bits_idx b (Suc n)) (Suc k)
          = bit_at n (bits_idx (b \<circ> Suc) n) k"
        unfolding eq by (rule bit_at_tail_lo[OF kn])
      also have "\<dots> = (b \<circ> Suc) k" by (rule Suc.IH[OF kn])
      finally show ?thesis using Suc by simp
    qed
  qed
qed

text \<open>The substitution carried by an index pair: x block on variables
  0..<s (MSB first), y block on variables s..<2s.\<close>

definition idx_subst :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, 'a::zero_neq_one) subst" where
  "idx_subst s x y j =
     (if j < s then Some (if bit_at s x j then 1 else 0)
      else if j < 2 * s then Some (if bit_at s y (j - s) then 1 else 0)
      else None)"

text \<open>Notation note: in this import context the TIGHT token sequence
  \<open>2*s\<close> fails inner-syntax parsing (an interaction along the imported
  Polynomials / HOL-Computational-Algebra chain), while the spaced form
  \<open>2 * s\<close> parses fine - hence explicit spacing in all interval terms
  below.  \<open>upt 0 (2 * s)\<close> is the exact variable-list shape consumed by
  the AFP theorems (\<open>set vs\<close> with \<open>vs = upt 0 (2 * s)\<close>).\<close>

lemma idx_subst_dom: "dom (idx_subst s x y) = set (upt 0 (2 * s))"
  by (auto simp add: idx_subst_def dom_def split: if_splits)

lemma idx_subst_ran: "ran (idx_subst s x y :: (nat, 'a::zero_neq_one) subst) \<subseteq> {0, 1}"
  by (auto simp add: idx_subst_def ran_def split: if_splits)

lemma idx_subst_in_substs:
  "idx_subst s x y \<in> substs (set (upt 0 (2 * s))) ({0, 1} :: 'a::zero_neq_one set)"
  by (simp add: substs_def idx_subst_dom idx_subst_ran)

lemma idx_subst_inj:
  fixes x x' y y' :: nat
  assumes bounds: "x < 2^s" "x' < 2^s" "y < 2^s" "y' < 2^s"
    and eq: "(idx_subst s x y :: (nat, 'a::zero_neq_one) subst) = idx_subst s x' y'"
  shows "x = x' \<and> y = y'"
proof
  have bx: "\<And>j. j < s \<Longrightarrow> bit_at s x j = bit_at s x' j"
  proof -
    fix j assume js: "j < s"
    from eq have "(idx_subst s x y :: (nat, 'a) subst) j = idx_subst s x' y' j" by simp
    then have "(if bit_at s x j then 1 else (0::'a)) = (if bit_at s x' j then 1 else 0)"
      using js by (simp add: idx_subst_def)
    then show "bit_at s x j = bit_at s x' j"
      by (metis (full_types) zero_neq_one)
  qed
  show "x = x'" using bit_at_complete[OF bounds(1) bounds(2)] bx by blast
  have by_: "\<And>j. j < s \<Longrightarrow> bit_at s y j = bit_at s y' j"
  proof -
    fix j assume js: "j < s"
    from eq have "(idx_subst s x y :: (nat, 'a) subst) (s + j) = idx_subst s x' y' (s + j)"
      by simp
    then have "(if bit_at s y j then 1 else (0::'a)) = (if bit_at s y' j then 1 else 0)"
      using js by (simp add: idx_subst_def)
    then show "bit_at s y j = bit_at s y' j"
      by (metis (full_types) zero_neq_one)
  qed
  show "y = y'" using bit_at_complete[OF bounds(3) bounds(4)] by_ by blast
qed

lemma idx_subst_surj:
  fixes \<sigma> :: "(nat, 'a::zero_neq_one) subst"
  assumes "\<sigma> \<in> substs (set (upt 0 (2 * s))) ({0, 1} :: 'a set)"
  shows "\<exists>x<2^s. \<exists>y<2^s. \<sigma> = idx_subst s x y"
proof -
  have dom\<sigma>: "dom \<sigma> = set (upt 0 (2 * s))" and ran\<sigma>: "ran \<sigma> \<subseteq> {0, 1}"
    using assms by (auto simp add: substs_def)
  define x where "x = bits_idx (\<lambda>j. \<sigma> j = Some 1) s"
  define y where "y = bits_idx (\<lambda>j. \<sigma> (s + j) = Some 1) s"
  have xs: "x < 2^s" and ys: "y < 2^s"
    by (simp_all add: x_def y_def bits_idx_lt)
  have val: "\<And>j. j < 2 * s \<Longrightarrow> \<sigma> j = Some 0 \<or> \<sigma> j = Some 1"
  proof -
    fix j assume "j < 2 * s"
    then have "j \<in> dom \<sigma>" using dom\<sigma> by simp
    then obtain v where v: "\<sigma> j = Some v" by (auto simp add: dom_def)
    then have "v \<in> ran \<sigma>" by (auto simp add: ran_def)
    then have "v = 0 \<or> v = 1" using ran\<sigma> by auto
    then show "\<sigma> j = Some 0 \<or> \<sigma> j = Some 1" using v by auto
  qed
  have "\<sigma> = idx_subst s x y"
  proof
    fix j
    show "\<sigma> j = idx_subst s x y j"
    proof (cases "j < s")
      case True
      then have bit: "bit_at s x j = (\<sigma> j = Some 1)"
        by (simp add: x_def bit_at_bits_idx)
      have "j < 2 * s" using True by simp
      then show ?thesis using val[of j] True bit
        by (auto simp add: idx_subst_def)
    next
      case False
      show ?thesis
      proof (cases "j < 2 * s")
        case True
        then have j2: "j = s + (j - s)" and js: "j - s < s" using False by simp_all
        have bit: "bit_at s y (j - s) = (\<sigma> (s + (j - s)) = Some 1)"
          by (simp add: y_def bit_at_bits_idx js)
        then show ?thesis using val[of j] False True j2
          by (auto simp add: idx_subst_def)
      next
        case False
        then have "\<sigma> j = None" using dom\<sigma> by (auto simp add: dom_def)
        then show ?thesis using \<open>\<not> j < s\<close> \<open>\<not> j < 2 * s\<close>
          by (simp add: idx_subst_def)
      qed
    qed
  qed
  then show ?thesis using xs ys by blast
qed

lemma bij_idx_subst:
  "bij_betw (\<lambda>(x, y). idx_subst s x y) ({..<2^s} \<times> {..<2^s})
            (substs (set (upt 0 (2 * s))) ({0, 1} :: 'a::zero_neq_one set))"
proof (rule bij_betw_imageI)
  show "inj_on (\<lambda>(x, y). idx_subst s x y :: (nat, 'a) subst) ({..<2^s} \<times> {..<2^s})"
    by (intro inj_onI) (auto dest: idx_subst_inj)
  show "(\<lambda>(x, y). idx_subst s x y :: (nat, 'a) subst) ` ({..<2^s} \<times> {..<2^s})
      = substs (set (upt 0 (2 * s))) {0, 1}"
  proof
    show "(\<lambda>(x, y). idx_subst s x y :: (nat, 'a) subst) ` ({..<2^s} \<times> {..<2^s})
        \<subseteq> substs (set (upt 0 (2 * s))) {0, 1}"
    proof
      fix \<sigma> :: "(nat, 'a) subst"
      assume "\<sigma> \<in> (\<lambda>(x, y). idx_subst s x y) ` ({..<2^s} \<times> {..<2^s})"
      then obtain x y where "\<sigma> = idx_subst s x y" by auto
      then show "\<sigma> \<in> substs (set (upt 0 (2 * s))) {0, 1}"
        using idx_subst_in_substs by simp
    qed
    show "substs (set (upt 0 (2 * s))) {0, 1}
        \<subseteq> (\<lambda>(x, y). idx_subst s x y :: (nat, 'a) subst) ` ({..<2^s} \<times> {..<2^s})"
    proof
      fix \<sigma> :: "(nat, 'a) subst" assume "\<sigma> \<in> substs (set (upt 0 (2 * s))) {0, 1}"
      then obtain x y where "x < 2^s" "y < 2^s" "\<sigma> = idx_subst s x y"
        using idx_subst_surj by blast
      then show "\<sigma> \<in> (\<lambda>(x, y). idx_subst s x y) ` ({..<2^s} \<times> {..<2^s})"
        by (auto simp add: image_def)
    qed
  qed
qed

lemma sum_substs_index:
  fixes G :: "(nat, 'a::zero_neq_one) subst \<Rightarrow> 'b::comm_monoid_add"
  shows "(\<Sum>\<sigma> \<in> substs (set (upt 0 (2 * s))) ({0, 1} :: 'a set). G \<sigma>)
       = (\<Sum>x<2^s. \<Sum>y<2^s. G (idx_subst s x y))"
proof -
  have "(\<Sum>\<sigma> \<in> substs (set (upt 0 (2 * s))) ({0, 1} :: 'a set). G \<sigma>)
      = (\<Sum>p \<in> {..<2^s} \<times> {..<2^s}. G (case p of (x, y) \<Rightarrow> idx_subst s x y))"
    by (rule sum.reindex_bij_betw[OF bij_idx_subst, symmetric])
  also have "\<dots> = (\<Sum>p \<in> {..<2^s} \<times> {..<2^s}. G (idx_subst s (fst p) (snd p)))"
    by (intro sum.cong refl) (simp add: split_def)
  also have "\<dots> = (\<Sum>x<2^s. \<Sum>y<2^s. G (idx_subst s x y))"
    by (simp add: sum.cartesian_product split_def)
  finally show ?thesis .
qed

section \<open>The layer sumcheck on the AFP protocol (B2)\<close>

text \<open>
  The bridge locale: the AFP abstract multivariate polynomial operations,
  with variables fixed to naturals and both the challenge type and the
  evaluation codomain fixed to one finite FIELD type 'a (the challenge
  field; KoalaBear degree-4 extension in production).  No axiom is added
  beyond the AFP locale, so every fact proved here is dischargeable in any
  AFP instance (no orphan assumptions); the connection to the layer
  identity is packaged in the definition \<open>layer_poly_repr\<close> and consumed as a
  theorem ASSUMPTION, discharged at instantiation time.
\<close>

locale gkr_layer_sumcheck =
  multi_variate_polynomial vars deg eval inst
  for vars :: "'p::comm_monoid_add \<Rightarrow> nat set"
  and deg :: "'p \<Rightarrow> nat"
  and eval :: "'p \<Rightarrow> (nat, 'a::{finite, field}) subst \<Rightarrow> 'a"
  and inst :: "'p \<Rightarrow> (nat, 'a) subst \<Rightarrow> 'p"
begin

text \<open>
  \<open>layer_poly_repr p L s claims below dbnd\<close>: the abstract polynomial p
  represents the layer sumcheck instance - variables in the 2s-cube
  (x block then y block), AFP degree at most dbnd, and boolean-hypercube
  evaluations equal to the layer integrand.  Only hypercube agreement is
  required: the sumcheck sum ranges over boolean substitutions, and the
  AFP round machinery never inspects non-boolean values of p itself.
\<close>

definition layer_poly_repr ::
  "'p \<Rightarrow> 'a layer \<Rightarrow> nat \<Rightarrow> ('a list \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where
  "layer_poly_repr p L s claims below dbnd \<longleftrightarrow>
     vars p \<subseteq> set (upt 0 (2 * s)) \<and> deg p \<le> dbnd \<and>
     (\<forall>x<2^s. \<forall>y<2^s. eval p (idx_subst s x y) = layer_integrand L s claims below x y)"

lemma layer_poly_repr_sum:
  assumes repr: "layer_poly_repr p L s claims below dbnd"
    and gates_in: "\<forall>g \<in> set (layer_gates L). g_in1 g < 2 ^ s \<and> g_in2 g < 2 ^ s"
  shows "(\<Sum>\<sigma> \<in> substs (set (upt 0 (2 * s))) ({0, 1} :: 'a set). eval p \<sigma>)
       = layer_claim_sum L claims below"
proof -
  have "(\<Sum>\<sigma> \<in> substs (set (upt 0 (2 * s))) ({0, 1} :: 'a set). eval p \<sigma>)
      = (\<Sum>x<2^s. \<Sum>y<2^s. eval p (idx_subst s x y))"
    by (rule sum_substs_index)
  also have "\<dots> = (\<Sum>x<2^s. \<Sum>y<2^s. layer_integrand L s claims below x y)"
    using repr by (intro sum.cong refl) (simp add: layer_poly_repr_def)
  also have "\<dots> = layer_claim_sum L claims below"
    by (rule layer_hypercube_identity[OF gates_in])
  finally show ?thesis .
qed

text \<open>
  B2 soundness: one layer reduction, AFP \<open>soundness_inductive\<close> consumed with
  vs = [0..<2s] and d = dbnd.  If the claimed value v differs from the true
  combined claim (the right side of the hypercube identity), then ANY
  prover makes the sumcheck verifier accept with probability at most
  2s * dbnd / |'a| over the uniformly drawn challenge tuple.
\<close>

theorem layer_sumcheck_soundness:
  assumes repr: "layer_poly_repr p L s claims below dbnd"
    and gates_in: "\<forall>g \<in> set (layer_gates L). g_in1 g < 2 ^ s \<and> g_in2 g < 2 ^ s"
    and false_claim: "v \<noteq> layer_claim_sum L claims below"
  shows "measure_pmf.prob (pmf_of_set (tuples UNIV (2 * s)))
           {rs. sumcheck pr ps ({0, 1}, p, v) r (zip (upt 0 (2 * s)) rs)}
       \<le> real (2 * s) * real dbnd / real CARD('a)"
proof -
  have vp: "vars p \<subseteq> set (upt 0 (2 * s))" and dp: "deg p \<le> dbnd"
    using repr by (auto simp add: layer_poly_repr_def)
  have neq: "v \<noteq> (\<Sum>\<sigma> \<in> substs (set (upt 0 (2 * s))) ({0, 1} :: 'a set). eval p \<sigma>)"
    using layer_poly_repr_sum[OF repr gates_in] false_claim by simp
  have set_eq: "{rs. sumcheck pr ps ({0, 1}, p, v) r (zip (upt 0 (2 * s)) rs)}
              = {rs. sumcheck pr ps ({0, 1}, p, v) r (zip (upt 0 (2 * s)) rs) \<and>
                     v \<noteq> (\<Sum>\<sigma> \<in> substs (set (upt 0 (2 * s))) ({0, 1} :: 'a set). eval p \<sigma>)}"
    using neq by auto
  have "measure_pmf.prob (pmf_of_set (tuples UNIV (length (upt 0 (2 * s)))))
          {rs. sumcheck pr ps ({0, 1}, p, v) r (zip (upt 0 (2 * s)) rs) \<and>
               v \<noteq> (\<Sum>\<sigma> \<in> substs (set (upt 0 (2 * s))) ({0, 1} :: 'a set). eval p \<sigma>)}
      \<le> real (length (upt 0 (2 * s))) * real dbnd / real CARD('a)"
    by (rule soundness_inductive[OF vp dp]) simp_all
  then show ?thesis by (simp add: set_eq)
qed

text \<open>
  Specialisation to the frozen per-round degree bound of the Rust verifier
  (reduce.rs \<open>LAYER_ROUND_DEGREE\<close> = 4): a representation with dbnd = 4 gives
  the design bound 2s * 4 / |'a| per layer.  Whether a given AFP instance
  admits a dbnd = 4 representation depends on that instance's degree
  measure (the AFP-shipped mpoly instance uses TOTAL degree, for which the
  representative has dbnd on the order of s; a max-per-variable-degree
  instance yields dbnd = 4).  The bound parameter keeps both dischargeable.
\<close>

corollary layer_sumcheck_soundness_deg4:
  assumes "layer_poly_repr p L s claims below 4"
    and "\<forall>g \<in> set (layer_gates L). g_in1 g < 2 ^ s \<and> g_in2 g < 2 ^ s"
    and "v \<noteq> layer_claim_sum L claims below"
  shows "measure_pmf.prob (pmf_of_set (tuples UNIV (2 * s)))
           {rs. sumcheck pr ps ({0, 1}, p, v) r (zip (upt 0 (2 * s)) rs)}
       \<le> real (2 * s) * 4 / real CARD('a)"
  using layer_sumcheck_soundness[OF assms] by simp

text \<open>
  B2 completeness (the honest-acceptance corollary of the hypercube
  identity): if the claimed value IS the true combined claim, the AFP
  honest prover passes every round for every challenge tuple.  Consumed
  from AFP \<open>completeness_inductive\<close>.
\<close>

theorem layer_sumcheck_completeness:
  assumes repr: "layer_poly_repr p L s claims below dbnd"
    and gates_in: "\<forall>g \<in> set (layer_gates L). g_in1 g < 2 ^ s \<and> g_in2 g < 2 ^ s"
    and true_claim: "v = layer_claim_sum L claims below"
    and len_rs: "length rs = 2 * s"
  shows "sumcheck honest_prover u ({0, 1}, p, v) r (zip (upt 0 (2 * s)) rs)"
proof -
  have fst_zip: "map fst (zip (upt 0 (2 * s)) rs) = (upt 0 (2 * s))"
    using len_rs by (simp add: map_fst_zip)
  have "v = (\<Sum>\<sigma> \<in> substs (set (map fst (zip (upt 0 (2 * s)) rs))) ({0, 1} :: 'a set). eval p \<sigma>)"
    using layer_poly_repr_sum[OF repr gates_in] true_claim by (simp add: fst_zip)
  moreover have "vars p \<subseteq> set (map fst (zip (upt 0 (2 * s)) rs))"
    using repr by (simp add: fst_zip layer_poly_repr_def)
  moreover have "distinct (map fst (zip (upt 0 (2 * s)) rs))"
    by (simp add: fst_zip)
  moreover have "({0, 1} :: 'a set) \<noteq> {}"
    by simp
  ultimately show ?thesis
    by (rule completeness_inductive)
qed

end

section \<open>Non-vacuity: the AFP mpoly instance inhabits the bridge locale\<close>

text \<open>
  The bridge locale adds no axioms, so the AFP concrete instantiation
  (mpoly with \<open>total_degree\<close>; \<open>Concrete_Multivariate_Polynomials\<close>) discharges
  it for any finite field challenge type.  This pins non-vacuity of the
  locale itself; an actual \<open>layer_poly_repr\<close> witness inside mpoly (the
  interpolation representative of the layer integrand, with total-degree
  bound 2s) is constructed in \<open>Layer_Representative\<close>.
\<close>

interpretation gkr_mpoly:
  gkr_layer_sumcheck "vars :: 'a::{finite, field} mpoly \<Rightarrow> nat set" total_degree
    "\<lambda>p \<sigma>. insertion (the \<circ> \<sigma>) p" inst
  by unfold_locales (auto simp add: multi_variate_polynomial_lemmas)

end
