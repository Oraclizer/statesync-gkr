(*
  Title:   GKR_Assembly.thy
  Session: GKR_Protocol (generic layer - no SMT / workload assumptions)

  Assembly layer of Theorem B: the pieces that connect the per-layer
  sumcheck instance (Sumcheck_Instance) into the layer-reduction chain of
  the GKR protocol (crate `ssgkr-protocol`, reduce.rs).

  Contents (Theorem B, layers B1 corollaries + B3 building blocks):

  - circuit_values_step: the defining recurrence of the witness value
    vectors (Rust `evaluate_circuit` / `CircuitWitness::layer_values`),
    in index form - the glue between per-layer statements and the chain.

  - gkr_layer_reduction_complete: the honest-acceptance corollary at chain
    position i - a claim built from the TRUE layer-i values (targets
    = V_i~(z_k), Rust verify's `targets`) is accepted by the AFP honest
    prover for every challenge tuple.

  - affine_root_prob / two_point_carry_prob / carried_claim_carry_sound:
    the two-point carry combination loss (reduce.rs: after each layer the
    two residual evaluations (eval_x, eval_y) become the next incoming
    claims combined as [(x*, 1), (y*, r)] with a fresh challenge r).  If
    either carried target is false, the combined claim collides with the
    true combined claim with probability at most 1/|'a| over r.  This is
    the per-layer union-bound summand "+ 1/CARD" of the B3 chain bound.

  # B3 chain (mechanized in this file)

  The full-chain statement is theorem gkr_assembly_soundness: if the
  claimed output table differs from the true circuit output, the chain
  bad event (defined by gkr_chain_bad, mirroring reduce.rs::verify's
  claim threading) has probability at most
  (s_out + sum over layers of (2 s_i * dbnd + 1)) / |'a| over the flat
  verifier randomness, for ANY adversary.  The per-layer summands are
  the AFP sumcheck soundness (via layer_sumcheck_soundness) and the
  two-point carry collision (carried_claim_carry_sound); the s_out seed
  is the multilinear Schwartz-Zippel bound (mle_agree_prob).  See the
  MODEL BOUNDARY note at gkr_chain_bad for the exact abstraction level
  (the bridge to the concrete verifier).

  # Probability model

  Interactive public-coin, identical to the AFP model.  Fiat-Shamir is
  outside the model (blackbox challenger assumption, design section B.3).
*)

theory GKR_Assembly
  imports Sumcheck_Instance
begin

section \<open>The chain recurrence of witness value vectors\<close>

text \<open>Value vector i is the layer-i evaluation of value vector i+1 (output
  layer first, Rust \<open>CircuitWitness::layer_values\<close> ordering).\<close>

lemma circuit_values_step:
  fixes Ls :: "'f::comm_ring_1 layer list"
  assumes "i < length Ls"
  shows "circuit_values Ls inputs ! i
       = layer_eval (Ls ! i) (circuit_values Ls inputs ! Suc i)"
  using assms
proof (induction Ls arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons L Ls)
  show ?case
  proof (cases i)
    case 0
    have ne: "circuit_values Ls inputs \<noteq> []" by (rule circuit_values_nonempty)
    show ?thesis
      by (simp add: 0 Let_def hd_conv_nth[OF ne])
  next
    case (Suc j)
    then have "j < length Ls" using Cons.prems by simp
    then show ?thesis
      by (simp add: Suc Let_def Cons.IH)
  qed
qed

section \<open>Honest acceptance at a chain position (B1 corollary, via B2)\<close>

context gkr_layer_sumcheck
begin

text \<open>
  At chain position i, the verifier's true targets are the MLE evaluations
  of the layer-i value vector (Rust: \<open>targets\<close> after the layer-i end
  check).  A claim value assembled from the true targets IS the layer
  claim sum for the layer-below value vector, so the honest prover is
  accepted on every challenge tuple.  This is the honest-prover
  acceptance corollary of the hypercube identity, lifted to the chain.
\<close>

theorem gkr_layer_reduction_complete:
  fixes Ls :: "'a layer list"
  assumes i_lt: "i < length Ls"
    and repr: "layer_poly_repr p (Ls ! i) s claims (circuit_values Ls inputs ! Suc i) dbnd"
    and gates_in: "\<forall>g \<in> set (layer_gates (Ls ! i)).
                     g_in1 g < 2 ^ s \<and> g_in2 g < 2 ^ s"
    and true_targets: "v = (\<Sum>(z, c)\<leftarrow>claims.
          c * (mle (layer_width_bits (Ls ! i)) ((!) (circuit_values Ls inputs ! i)) z
               - const_mle (Ls ! i) z))"
    and len_rs: "length rs = 2 * s"
  shows "sumcheck honest_prover u ({0, 1}, p, v) r (zip (upt 0 (2 * s)) rs)"
proof -
  have "v = layer_claim_sum (Ls ! i) claims (circuit_values Ls inputs ! Suc i)"
    unfolding true_targets layer_claim_sum_def
    by (simp add: circuit_values_step[OF i_lt])
  then show ?thesis
    using layer_sumcheck_completeness[OF repr gates_in _ len_rs] by simp
qed

end

section \<open>Two-point carry combination (B3 building block)\<close>

text \<open>
  A nonzero affine polynomial in one fresh uniform challenge vanishes with
  probability at most 1/|'a| (one root if the slope is nonzero, none
  otherwise).
\<close>

lemma affine_root_prob:
  fixes a b :: "'a::{finite, field}"
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
  shows "measure_pmf.prob (pmf_of_set (UNIV :: 'a set)) {r. a + r * b = 0}
       \<le> 1 / real CARD('a)"
proof (cases "b = 0")
  case True
  with assms have "a \<noteq> 0" by simp
  then have "{r :: 'a. a + r * b = 0} = {}" using True by simp
  then show ?thesis by simp
next
  case False
  have "{r :: 'a. a + r * b = 0} = {- (a / b)}"
  proof
    show "{r :: 'a. a + r * b = 0} \<subseteq> {- (a / b)}"
    proof
      fix r :: 'a assume "r \<in> {r. a + r * b = 0}"
      then have "r * b = - a" by (simp add: eq_neg_iff_add_eq_0 add.commute)
      with False have "r = - a / b" by (metis eq_divide_imp mult.commute)
      then show "r \<in> {- (a / b)}" by (simp add: divide_minus_left)
    qed
    show "{- (a / b)} \<subseteq> {r :: 'a. a + r * b = 0}"
      using False by (auto simp add: field_simps)
  qed
  then show ?thesis
    by (simp add: measure_pmf_of_set)
qed

text \<open>
  The carry step of reduce.rs: after layer i the residual evaluations
  (\<open>eval_x\<close> at x*, \<open>eval_y\<close> at y*) become the next incoming claims, combined
  with coefficients (1, r) for a fresh challenge r.  If either claimed
  target differs from the true one, the combined claims collide with
  probability at most 1/|'a| over r.
\<close>

lemma two_point_carry_prob:
  fixes tx ty vx vy :: "'a::{finite, field}"
  assumes "tx \<noteq> vx \<or> ty \<noteq> vy"
  shows "measure_pmf.prob (pmf_of_set (UNIV :: 'a set))
           {r. tx + r * ty = vx + r * vy}
       \<le> 1 / real CARD('a)"
proof -
  have eq: "{r :: 'a. tx + r * ty = vx + r * vy}
          = {r. (tx - vx) + r * (ty - vy) = 0}"
    by (auto simp add: algebra_simps)
  have "tx - vx \<noteq> 0 \<or> ty - vy \<noteq> 0" using assms by auto
  then show ?thesis unfolding eq by (rule affine_root_prob)
qed

text \<open>
  The same, phrased against the layer claim sum: a carried claim value
  assembled from FALSE targets (tx, ty) equals the true combined claim
  \<open>layer_claim_sum L [(x*, 1), (y*, r)] below\<close> with probability at most
  1/|'a| over the fresh combination challenge r.  This is the per-layer
  "+1/CARD" summand of the B3 union bound.
\<close>

lemma carried_claim_carry_sound:
  fixes L :: "'a::{finite, field} layer" and below :: "'a list"
  assumes "tx \<noteq> mle (layer_width_bits L) ((!) (layer_eval L below)) xstar \<or>
           ty \<noteq> mle (layer_width_bits L) ((!) (layer_eval L below)) ystar"
  shows "measure_pmf.prob (pmf_of_set (UNIV :: 'a set))
           {r. (tx - const_mle L xstar) + r * (ty - const_mle L ystar)
             = layer_claim_sum L [(xstar, 1), (ystar, r)] below}
       \<le> 1 / real CARD('a)"
proof -
  let ?M = "\<lambda>zpt. mle (layer_width_bits L) ((!) (layer_eval L below)) zpt"
  have expand: "\<And>r. layer_claim_sum L [(xstar, 1), (ystar, r)] below
      = (?M xstar - const_mle L xstar) + r * (?M ystar - const_mle L ystar)"
    by (simp add: layer_claim_sum_def)
  have set_eq: "{r. (tx - const_mle L xstar) + r * (ty - const_mle L ystar)
                  = layer_claim_sum L [(xstar, 1), (ystar, r)] below}
              = {r. tx + r * ty = ?M xstar + r * ?M ystar}"
    unfolding expand by (auto simp add: algebra_simps)
  show ?thesis unfolding set_eq
    by (rule two_point_carry_prob) (use assms in auto)
qed

section \<open>Multilinear Schwartz-Zippel over point tuples (B3 building block)\<close>

text \<open>
  Head-coordinate decomposition of the MLE: at a point \<open>p # ps\<close> the MLE is
  AFFINE in the head coordinate p, interpolating between the low-half and
  high-half tables (variable 0 is the MSB, matching poly.rs binding).
\<close>

lemma mle_cons:
  fixes p :: "'f::comm_ring_1" and ps :: "'f list"
  assumes len: "length ps = n"
  shows "mle (Suc n) f (p # ps)
       = (1 - p) * mle n f ps + p * mle n (\<lambda>i. f (i + 2 ^ n)) ps"
proof -
  have split2: "{..<(2::nat) ^ Suc n} = {..<2 ^ n} \<union> (\<lambda>i. i + 2 ^ n) ` {..<2 ^ n}"
  proof
    show "{..<(2::nat) ^ Suc n} \<subseteq> {..<2 ^ n} \<union> (\<lambda>i. i + 2 ^ n) ` {..<2 ^ n}"
    proof
      fix x assume "x \<in> {..<(2::nat) ^ Suc n}"
      then have "x < 2 * 2 ^ n" by simp
      then show "x \<in> {..<2 ^ n} \<union> (\<lambda>i. i + 2 ^ n) ` {..<2 ^ n}"
      proof (cases "x < 2 ^ n")
        case False
        then have "x - 2 ^ n < 2 ^ n" and "x = (x - 2 ^ n) + 2 ^ n"
          using \<open>x < 2 * 2 ^ n\<close> by simp_all
        then show ?thesis by force
      qed simp
    qed
    show "{..<2 ^ n} \<union> (\<lambda>i. i + 2 ^ n) ` {..<2 ^ n} \<subseteq> {..<(2::nat) ^ Suc n}"
      by auto
  qed
  have inj: "inj_on (\<lambda>i. i + (2::nat) ^ n) {..<2 ^ n}"
    by (simp add: inj_on_def)
  have disj: "{..<(2::nat) ^ n} \<inter> (\<lambda>i. i + 2 ^ n) ` {..<2 ^ n} = {}"
    by auto
  have "mle (Suc n) f (p # ps) = (\<Sum>idx \<in> {..<2 ^ Suc n}. eq_pi (p # ps) idx * f idx)"
    by (simp add: mle_def)
  also have "\<dots> = (\<Sum>idx<2 ^ n. eq_pi (p # ps) idx * f idx)
                + (\<Sum>idx<2 ^ n. eq_pi (p # ps) (idx + 2 ^ n) * f (idx + 2 ^ n))"
    by (subst split2) (simp add: sum.union_disjoint disj inj sum.reindex)
  also have "\<dots> = (1 - p) * (\<Sum>idx<2 ^ n. eq_pi ps idx * f idx)
                + p * (\<Sum>idx<2 ^ n. eq_pi ps idx * f (idx + 2 ^ n))"
  proof -
    have lo: "(\<Sum>idx<2 ^ n. eq_pi (p # ps) idx * f idx)
            = (\<Sum>idx<2 ^ n. (1 - p) * (eq_pi ps idx * f idx))"
    proof (intro sum.cong refl)
      fix idx :: nat assume "idx \<in> {..<2 ^ n}"
      then have "idx < 2 ^ length ps" using len by simp
      then show "eq_pi (p # ps) idx * f idx = (1 - p) * (eq_pi ps idx * f idx)"
        by (simp add: eq_pi_cons_lo mult.assoc)
    qed
    have hi: "(\<Sum>idx<2 ^ n. eq_pi (p # ps) (idx + 2 ^ n) * f (idx + 2 ^ n))
            = (\<Sum>idx<2 ^ n. p * (eq_pi ps idx * f (idx + 2 ^ n)))"
    proof (intro sum.cong refl)
      fix idx :: nat assume "idx \<in> {..<2 ^ n}"
      then have idxlt: "idx < 2 ^ length ps" using len by simp
      have "eq_pi (p # ps) (idx + 2 ^ n) = p * eq_pi ps idx"
        using eq_pi_cons_hi[OF idxlt] len by simp
      then show "eq_pi (p # ps) (idx + 2 ^ n) * f (idx + 2 ^ n)
               = p * (eq_pi ps idx * f (idx + 2 ^ n))"
        by (simp add: mult.assoc)
    qed
    show ?thesis by (simp add: lo hi sum_distrib_left)
  qed
  also have "\<dots> = (1 - p) * mle n f ps + p * mle n (\<lambda>i. f (i + 2 ^ n)) ps"
    by (simp add: mle_def)
  finally show ?thesis .
qed

text \<open>
  Schwartz-Zippel for multilinear value tables: a not-identically-zero
  table has a vanishing MLE at a uniformly random point tuple with
  probability at most n/|'a|.  This is the output-layer seed of the B3
  chain (the claimed-output MLE vs the true output MLE at the random
  \<open>z_0\<close>), phrased over the difference table.  Proof mirrors the AFP
  \<open>soundness_inductive\<close> recursion: fix the head coordinate, at most ONE
  head value can make the residual table identically zero, and the
  induction hypothesis covers the rest.
\<close>

lemma mle_zero_prob:
  fixes f :: "nat \<Rightarrow> 'a::{finite, field}"
  assumes "\<exists>idx<2 ^ n. f idx \<noteq> 0"
  shows "measure_pmf.prob (pmf_of_set (tuples UNIV n)) {zs. mle n f zs = 0}
       \<le> real n / real CARD('a)"
  using assms
proof (induction n arbitrary: f)
  case 0
  then have f0: "f 0 \<noteq> 0" by auto
  have t0: "tuples (UNIV :: 'a set) 0 = {[]}" by (rule tuples_Zero)
  have "mle 0 f ([] :: 'a list) = f 0" by (simp add: mle_def)
  then have "{[] :: 'a list} \<inter> {zs. mle 0 f zs = 0} = {}" using f0 by auto
  then have "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) 0))
               {zs. mle 0 f zs = 0} = 0"
    by (simp add: t0 measure_pmf_of_set)
  then show ?case by simp
next
  case (Suc n)
  let ?q = "real CARD('a)"
  let ?g = "\<lambda>a i. (1 - a) * f i + a * f (i + 2 ^ n)"
  let ?P = "\<lambda>a. measure_pmf.prob (pmf_of_set (tuples UNIV n)) {rs. mle n (?g a) rs = 0}"

  have q_pos: "0 < ?q" by (simp add: card_gt_0_iff)

  \<comment> \<open>fix the head coordinate\<close>
  have "measure_pmf.prob (pmf_of_set (tuples UNIV (Suc n))) {zs. mle (Suc n) f zs = 0}
      = (\<Sum>a\<in>(UNIV::'a set).
           measure_pmf.prob (pmf_of_set (tuples UNIV n)) {rs. mle (Suc n) f (a # rs) = 0})
        / ?q"
    by (rule prob_tuples_fixed_hd)

  \<comment> \<open>on the support, the head-fixed MLE is the MLE of the blended table\<close>
  moreover have blend: "\<And>a. measure_pmf.prob (pmf_of_set (tuples UNIV n))
                    {rs. mle (Suc n) f (a # rs) = 0} = ?P a"
  proof -
    fix a :: 'a
    have "measure_pmf.prob (pmf_of_set (tuples UNIV n)) {rs. mle (Suc n) f (a # rs) = 0}
        = measure_pmf.prob (pmf_of_set (tuples UNIV n)) {rs. mle n (?g a) rs = 0}"
    proof (rule prob_cong)
      fix rs :: "'a list" assume "rs \<in> set_pmf (pmf_of_set (tuples UNIV n))"
      then have "rs \<in> tuples (UNIV :: 'a set) n"
        by (simp add: set_pmf_of_set tuples_finite)
      then have len: "length rs = n" by (auto)
      have "mle (Suc n) f (a # rs)
          = (1 - a) * mle n f rs + a * mle n (\<lambda>i. f (i + 2 ^ n)) rs"
        by (rule mle_cons[OF len])
      also have "\<dots> = mle n (?g a) rs"
      proof -
        have "mle n (?g a) rs
            = mle n (\<lambda>i. (1 - a) * f i) rs + mle n (\<lambda>i. a * f (i + 2 ^ n)) rs"
          using mle_add[of n "\<lambda>i. (1 - a) * f i" "\<lambda>i. a * f (i + 2 ^ n)" rs] by simp
        also have "\<dots> = (1 - a) * mle n f rs + a * mle n (\<lambda>i. f (i + 2 ^ n)) rs"
          by (simp add: mle_scale)
        finally show ?thesis by simp
      qed
      finally show "(rs \<in> {rs. mle (Suc n) f (a # rs) = 0})
                  = (rs \<in> {rs. mle n (?g a) rs = 0})" by simp
    qed
    then show "measure_pmf.prob (pmf_of_set (tuples UNIV n))
                 {rs. mle (Suc n) f (a # rs) = 0} = ?P a" by simp
  qed

  \<comment> \<open>at most one head value blends the table to identically zero\<close>
  moreover have "(\<Sum>a\<in>(UNIV::'a set). ?P a) \<le> real n + 1"
  proof -
    obtain i0 where i0: "i0 < 2 ^ Suc n" "f i0 \<noteq> 0" using Suc.prems by auto
    obtain j where j: "j < 2 ^ n" and jnz: "f j \<noteq> 0 \<or> f (j + 2 ^ n) \<noteq> 0"
    proof (cases "i0 < 2 ^ n")
      case True
      then show ?thesis using i0 that[of i0] by auto
    next
      case False
      have "i0 - 2 ^ n < 2 ^ n" using i0(1) False by simp
      moreover have "(i0 - 2 ^ n) + 2 ^ n = i0" using False by simp
      ultimately show ?thesis using i0(2) that[of "i0 - 2 ^ n"] by auto
    qed
    have bad_sub: "{a. \<forall>i<2 ^ n. ?g a i = 0} \<subseteq> {a. ?g a j = 0}"
      using j by auto
    have bad_card: "card {a :: 'a. ?g a j = 0} \<le> 1"
    proof (cases "f (j + 2 ^ n) = f j")
      case True
      then have "\<And>a. ?g a j = f j" by (simp add: algebra_simps)
      moreover have "f j \<noteq> 0" using True jnz by auto
      ultimately have "{a :: 'a. ?g a j = 0} = {}" by simp
      then show ?thesis by simp
    next
      case False
      have "{a :: 'a. ?g a j = 0} \<subseteq> {f j / (f j - f (j + 2 ^ n))}"
      proof
        fix a assume "a \<in> {a. ?g a j = 0}"
        then have "f j + a * (f (j + 2 ^ n) - f j) = 0" by (simp add: algebra_simps)
        then have "a * (f j - f (j + 2 ^ n)) = f j" by (simp add: algebra_simps)
        then have "a = f j / (f j - f (j + 2 ^ n))"
          using False by (metis eq_divide_imp right_minus_eq)
        then show "a \<in> {f j / (f j - f (j + 2 ^ n))}" by simp
      qed
      then have "card {a :: 'a. ?g a j = 0}
               \<le> card {f j / (f j - f (j + 2 ^ n))}"
        using card_mono[of "{f j / (f j - f (j + 2 ^ n))}" "{a. ?g a j = 0}"]
        by simp
      then show ?thesis by simp
    qed
    have IH_good: "\<And>a. \<exists>i<2 ^ n. ?g a i \<noteq> 0 \<Longrightarrow> ?P a \<le> real n / ?q"
      by (rule Suc.IH)
    have P_le_1: "\<And>a. ?P a \<le> 1"
      by (rule measure_pmf.prob_le_1)
    have "(\<Sum>a\<in>(UNIV::'a set). ?P a)
        \<le> (\<Sum>a\<in>(UNIV::'a set). if \<forall>i<2 ^ n. ?g a i = 0 then 1 else real n / ?q)"
    proof (intro sum_mono)
      fix a :: 'a assume "a \<in> UNIV"
      show "?P a \<le> (if \<forall>i<2 ^ n. ?g a i = 0 then 1 else real n / ?q)"
      proof (cases "\<forall>i<2 ^ n. ?g a i = 0")
        case True
        then show ?thesis using P_le_1 by simp
      next
        case False
        then have "\<exists>i<2 ^ n. ?g a i \<noteq> 0" by auto
        then show ?thesis using IH_good by simp
      qed
    qed
    also have "\<dots> = (\<Sum>a \<in> {a :: 'a. \<forall>i<2 ^ n. ?g a i = 0}. 1)
                  + (\<Sum>a \<in> (UNIV :: 'a set) - {a. \<forall>i<2 ^ n. ?g a i = 0}. real n / ?q)"
    proof -
      have set_eq: "{a :: 'a. \<exists>i<2 ^ n. ?g a i \<noteq> 0}
                  = (UNIV :: 'a set) - {a. \<forall>i<2 ^ n. ?g a i = 0}"
        by auto
      show ?thesis
        by (subst sum.If_cases) (simp_all add: set_eq Compl_eq_Diff_UNIV)
    qed
    also have "\<dots> \<le> 1 + real CARD('a) * (real n / ?q)"
    proof -
      have "(\<Sum>a \<in> {a :: 'a. \<forall>i<2 ^ n. ?g a i = 0}. (1::real))
          = real (card {a :: 'a. \<forall>i<2 ^ n. ?g a i = 0})" by simp
      also have "\<dots> \<le> 1"
        using card_mono[OF _ bad_sub] bad_card
        by (smt (verit) of_nat_le_1_iff finite_code le_trans)
      finally have first: "(\<Sum>a \<in> {a :: 'a. \<forall>i<2 ^ n. ?g a i = 0}. (1::real)) \<le> 1" .
      have "(\<Sum>a \<in> (UNIV :: 'a set) - {a. \<forall>i<2 ^ n. ?g a i = 0}. real n / ?q)
          = real (card ((UNIV :: 'a set) - {a. \<forall>i<2 ^ n. ?g a i = 0})) * (real n / ?q)"
        by simp
      also have "\<dots> \<le> real CARD('a) * (real n / ?q)"
        by (intro mult_right_mono) (simp_all add: card_mono)
      finally have second: "(\<Sum>a \<in> (UNIV :: 'a set) - {a. \<forall>i<2 ^ n. ?g a i = 0}. real n / ?q)
          \<le> real CARD('a) * (real n / ?q)" .
      show ?thesis using first second by simp
    qed
    also have "\<dots> = real n + 1" using q_pos by simp
    finally show ?thesis by simp
  qed
  ultimately have "measure_pmf.prob (pmf_of_set (tuples UNIV (Suc n)))
                     {zs. mle (Suc n) f zs = 0} \<le> (real n + 1) / ?q"
    by (simp add: divide_right_mono)
  then show ?case by (simp add: add.commute)
qed

text \<open>
  The output-layer seed in two-table form: if the claimed output table
  differs anywhere on the cube from the true one, their MLEs agree at a
  uniformly random \<open>z_0\<close> tuple with probability at most n/|'a|
  (reduce.rs::verify draws \<open>z_0\<close> and evaluates the claimed-output MLE m0;
  the chain starts from the claim \<open>V_0\<close>~(\<open>z_0\<close>) = m0).
\<close>

lemma mle_agree_prob:
  fixes f g :: "nat \<Rightarrow> 'a::{finite, field}"
  assumes "\<exists>idx<2 ^ n. f idx \<noteq> g idx"
  shows "measure_pmf.prob (pmf_of_set (tuples UNIV n)) {zs. mle n f zs = mle n g zs}
       \<le> real n / real CARD('a)"
proof -
  have diff: "\<exists>idx<2 ^ n. f idx - g idx \<noteq> 0"
    using assms by auto
  have "{zs :: 'a list. mle n f zs = mle n g zs} = {zs. mle n (\<lambda>i. f i - g i) zs = 0}"
  proof -
    have "\<And>zs :: 'a list. mle n (\<lambda>i. f i - g i) zs = mle n f zs - mle n g zs"
      by (simp add: mle_def sum_subtractf algebra_simps)
    then show ?thesis by auto
  qed
  then show ?thesis
    using mle_zero_prob[OF diff] by simp
qed

section \<open>Tuple-space splitting tools (B3 probability plumbing)\<close>

text \<open>
  The AFP Probability\_Tools provide single-head splitting
  (@{thm [source] prob_tuples_fixed_hd}).  The chain bound consumes
  per-layer SEGMENTS of the flat challenge tuple, so we derive the
  k-element generalisation, its prefix-marginal corollary, and the
  single-coordinate bridge to a plain uniform draw.
\<close>

lemma card_tuples_UNIV: "card (tuples (UNIV :: 'a::finite set) n) = CARD('a) ^ n"
  unfolding tuples_def
  using card_lists_length_eq[of "UNIV :: 'a set"] by simp

lemma prob_tuples_split_seg:
  fixes E :: "'a::finite list \<Rightarrow> bool"
  shows "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (k + m))) {zs. E zs}
       = (\<Sum>xs \<in> tuples (UNIV :: 'a set) k.
            measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) m)) {ys. E (xs @ ys)})
         / real (CARD('a)) ^ k"
proof (induction k arbitrary: E)
  case 0
  show ?case by (simp add: tuples_Zero)
next
  case (Suc k)
  have hd_split:
    "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (Suc (k + m)))) {zs. E zs}
     = (\<Sum>a \<in> (UNIV :: 'a set).
          measure_pmf.prob (pmf_of_set (tuples UNIV (k + m))) {rs. E (a # rs)})
       / real CARD('a)"
    by (rule prob_tuples_fixed_hd)
  have IHa: "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (k + m))) {rs. E (a # rs)}
     = (\<Sum>xs \<in> tuples (UNIV :: 'a set) k.
          measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) m)) {ys. E (a # xs @ ys)})
       / real (CARD('a)) ^ k" for a
    by (rule Suc.IH)
  have bij: "bij_betw (\<lambda>(a, xs). a # xs) ((UNIV :: 'a set) \<times> tuples (UNIV :: 'a set) k)
                      (tuples (UNIV :: 'a set) (Suc k))"
    by (intro bij_betw_imageI) (auto simp add: inj_on_def tuples_Suc)
  have reindex:
    "(\<Sum>xs' \<in> tuples (UNIV :: 'a set) (Suc k).
        measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) m)) {ys. E (xs' @ ys)})
     = (\<Sum>p \<in> (UNIV :: 'a set) \<times> tuples (UNIV :: 'a set) k.
          measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) m))
            {ys. E ((case p of (a, xs) \<Rightarrow> a # xs) @ ys)})"
    by (rule sum.reindex_bij_betw[OF bij, symmetric])
  have prod_sum:
    "(\<Sum>p \<in> (UNIV :: 'a set) \<times> tuples (UNIV :: 'a set) k.
        measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) m))
          {ys. E ((case p of (a, xs) \<Rightarrow> a # xs) @ ys)})
     = (\<Sum>a \<in> (UNIV :: 'a set). \<Sum>xs \<in> tuples (UNIV :: 'a set) k.
          measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) m)) {ys. E (a # xs @ ys)})"
    by (simp add: sum.cartesian_product case_prod_beta)
  have "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (Suc k + m))) {zs. E zs}
      = (\<Sum>a \<in> (UNIV :: 'a set).
           (\<Sum>xs \<in> tuples (UNIV :: 'a set) k.
              measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) m)) {ys. E (a # xs @ ys)})
           / real (CARD('a)) ^ k) / real CARD('a)"
    using hd_split IHa by simp
  also have "\<dots> = (\<Sum>a \<in> (UNIV :: 'a set). \<Sum>xs \<in> tuples (UNIV :: 'a set) k.
                     measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) m))
                       {ys. E (a # xs @ ys)})
                  / real (CARD('a)) ^ k / real CARD('a)"
    by (simp add: sum_divide_distrib)
  also have "\<dots> = (\<Sum>xs' \<in> tuples (UNIV :: 'a set) (Suc k).
                     measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) m))
                       {ys. E (xs' @ ys)})
                  / real (CARD('a)) ^ Suc k"
    unfolding reindex prod_sum by (simp add: divide_divide_eq_left mult.commute)
  finally show ?case by simp
qed

lemma prob_tuples_prefix:
  fixes E :: "'a::finite list \<Rightarrow> bool"
  shows "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (k + m))) {zs. E (take k zs)}
       = measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) k)) {xs. E xs}"
proof -
  have per: "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) m))
               {ys. E (take k (xs @ ys))}
           = (if E xs then 1 else 0)" if xs: "xs \<in> tuples (UNIV :: 'a set) k" for xs
  proof -
    from xs have len: "length xs = k" by auto
    have tk: "take k (xs @ ys) = xs" for ys :: "'a list"
      using len by simp
    show ?thesis
    proof (cases "E xs")
      case True
      then have "{ys :: 'a list. E (take k (xs @ ys))} = UNIV" using tk by auto
      then show ?thesis
        using True by (simp add: measure_pmf_of_set)
    next
      case False
      then have "{ys :: 'a list. E (take k (xs @ ys))} = {}" using tk by auto
      then show ?thesis using False by simp
    qed
  qed
  have "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (k + m))) {zs. E (take k zs)}
      = (\<Sum>xs \<in> tuples (UNIV :: 'a set) k.
           measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) m)) {ys. E (take k (xs @ ys))})
        / real (CARD('a)) ^ k"
    by (rule prob_tuples_split_seg)
  also have "\<dots> = (\<Sum>xs \<in> tuples (UNIV :: 'a set) k. if E xs then 1 else 0)
                  / real (CARD('a)) ^ k"
    by (intro arg_cong2[where f = "(/)"] sum.cong refl per)
  also have "\<dots> = real (card (tuples (UNIV :: 'a set) k \<inter> {xs. E xs}))
                  / real (CARD('a)) ^ k"
  proof -
    have "(\<Sum>xs \<in> tuples (UNIV :: 'a set) k. if E xs then (1::real) else 0)
        = (\<Sum>xs \<in> tuples (UNIV :: 'a set) k \<inter> {xs. E xs}. 1)"
      by (subst sum.If_cases) simp_all
    then show ?thesis by simp
  qed
  also have "\<dots> = measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) k)) {xs. E xs}"
    by (simp add: measure_pmf_of_set card_tuples_UNIV)
  finally show ?thesis .
qed

lemma prob_tuples_single:
  fixes Q :: "'a::finite \<Rightarrow> bool"
  shows "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) 1)) {ys. Q (ys ! 0)}
       = measure_pmf.prob (pmf_of_set (UNIV :: 'a set)) {r. Q r}"
proof -
  have z: "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) 0))
             (if Q a then UNIV else {}) = (if Q a then 1 else 0)" for a :: 'a
    by (cases "Q a") (simp_all add: tuples_Zero measure_pmf_of_set)
  have "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (Suc 0))) {ys. Q (ys ! 0)}
      = (\<Sum>a \<in> (UNIV :: 'a set).
           measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) 0)) {rs. Q ((a # rs) ! 0)})
        / real CARD('a)"
    by (rule prob_tuples_fixed_hd)
  also have "\<dots> = (\<Sum>a \<in> (UNIV :: 'a set). if Q a then 1 else 0) / real CARD('a)"
    by (simp add: z)
  also have "\<dots> = real (card ((UNIV :: 'a set) \<inter> {r. Q r})) / real CARD('a)"
    by (subst sum.If_cases) simp_all
  also have "\<dots> = measure_pmf.prob (pmf_of_set (UNIV :: 'a set)) {r. Q r}"
    by (simp add: measure_pmf_of_set)
  finally show ?thesis by simp
qed

section \<open>The layer-reduction chain event (B3)\<close>

text \<open>
  The chain randomness is one flat tuple: per layer, \<open>2 s\<close> sumcheck
  challenges followed by ONE carry challenge (reduce.rs::verify samples
  \<open>r\<close> after observing the carried evaluations).  \<open>chain_rlen\<close> is its
  total length; \<open>gkr_chain_wf\<close> pins the shape invariants of the layer
  chain: gate fan-in inside the below-cube, the head width being the
  next layer's width (reduce.rs \<open>s_in\<close>), and the below vector being the
  next layer's evaluation (the defining recurrence of \<open>circuit_values\<close>).
\<close>

definition chain_rlen :: "nat list \<Rightarrow> nat" where
  "chain_rlen ss = (\<Sum>s\<leftarrow>ss. 2 * s + 1)"

lemma chain_rlen_simps [simp]:
  "chain_rlen [] = 0"
  "chain_rlen (s # ss) = 2 * s + 1 + chain_rlen ss"
  by (simp_all add: chain_rlen_def)

fun gkr_chain_wf :: "nat list \<Rightarrow> 'f::comm_ring_1 layer list \<Rightarrow> 'f list list \<Rightarrow> bool" where
  "gkr_chain_wf [] [] [] \<longleftrightarrow> True"
| "gkr_chain_wf [s] [L] [b] \<longleftrightarrow>
     (\<forall>g \<in> set (layer_gates L). g_in1 g < 2 ^ s \<and> g_in2 g < 2 ^ s)"
| "gkr_chain_wf (s # s' # ss) (L # L' # Ls) (b # b' # bs) \<longleftrightarrow>
     (\<forall>g \<in> set (layer_gates L). g_in1 g < 2 ^ s \<and> g_in2 g < 2 ^ s) \<and>
     s = layer_width_bits L' \<and> b = layer_eval L' b' \<and>
     gkr_chain_wf (s' # ss) (L' # Ls) (b' # bs)"
| "gkr_chain_wf ss Ls bels \<longleftrightarrow> False"

text \<open>
  The chain BAD event, for an arbitrary adversary.  The adversary \<open>A\<close>
  supplies, per layer index and per randomness prefix, an AFP prover
  (with its state and previous-challenge input) and the two carried
  evaluations \<open>(tx, ty)\<close> (reduce.rs: \<open>lp.eval_x\<close>/\<open>lp.eval_y\<close>) - the
  prover triple read at the layer entry (empty local prefix), the
  carried evaluations after the layer's sumcheck challenges.  Per layer
  the event is:

  \<^item> the AFP sumcheck for the TRUE layer polynomial (the representative
    \<open>P L s claims b\<close>) accepts the incoming claim value \<open>v\<close>, OR
  \<^item> the carried evaluations are FALSE (differ from the below-vector MLE
    at the drawn point \<open>(x*, y*)\<close>) and the chain continues on the next
    incoming claim \<open>[(x*, 1), (y*, r)]\<close> with claim value
    \<open>(tx - const~(x*)) + r (ty - const~(y*))\<close> - literally
    reduce.rs::verify's carry.

  MODEL BOUNDARY (the bridge to the concrete verifier, recorded): the REAL verifier's layer
  acceptance implies this event.  Its final check compares the
  sumcheck's residual value against the wiring-MLE reconstruction at
  \<open>(x*, y*)\<close> assembled from \<open>(tx, ty)\<close>; when \<open>(tx, ty)\<close> are the true
  below-MLE evaluations, that reconstruction IS the representative
  polynomial's value at the challenge point (the representative agrees
  with the layer integrand as a polynomial, which the concrete mpoly
  representative realises at instantiation), so rounds + final check
  amount to AFP sumcheck acceptance; otherwise the carried evaluations
  are false, which is the second disjunct.  At the LAST layer the
  carried evaluations are checked directly against the verifier-computed
  input MLE (lib.rs input-claim discharge, seal S-4), so a false carry
  is rejected deterministically - hence no continuation disjunct there.
\<close>

section \<open>The chain union bound (B3)\<close>

context gkr_layer_sumcheck
begin

fun gkr_chain_bad ::
  "('a layer \<Rightarrow> nat \<Rightarrow> ('a list \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'p)
   \<Rightarrow> (nat \<Rightarrow> 'a list \<Rightarrow> ('p, 'a, 'a, nat, 's) prover \<times> 's \<times> 'a \<times> 'a \<times> 'a)
   \<Rightarrow> nat list \<Rightarrow> 'a layer list \<Rightarrow> 'a list list
   \<Rightarrow> ('a list \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "gkr_chain_bad P A (s # ss) (L # Ls) (b # bs) claims v rs =
     ((case A 0 [] of (pr, ps, r0, tx0, ty0) \<Rightarrow>
         sumcheck pr ps ({0, 1}, P L s claims b, v) r0
                  (zip (upt 0 (2 * s)) (take (2 * s) rs)))
      \<or> (Ls \<noteq> [] \<and>
         (case A 0 (take (2 * s) rs) of (pr1, ps1, r1, tx, ty) \<Rightarrow>
            (tx \<noteq> mle s ((!) b) (take s rs) \<or>
             ty \<noteq> mle s ((!) b) (take s (drop s rs))) \<and>
            gkr_chain_bad P (\<lambda>j pfx. A (Suc j) (take (2 * s + 1) rs @ pfx)) ss Ls bs
              [(take s rs, 1), (take s (drop s rs), rs ! (2 * s))]
              ((tx - const_mle (hd Ls) (take s rs))
               + rs ! (2 * s) * (ty - const_mle (hd Ls) (take s (drop s rs))))
              (drop (2 * s + 1) rs))))"
| "gkr_chain_bad P A ss Ls bels claims v rs = False"

text \<open>
  The chain event is unfolded ONLY where a proof explicitly says so:
  under the default simpset the recursive equation would re-expand
  nested occurrences and normalise the take/drop plumbing of the
  adversary reindexing into mismatched forms (the environment-sensitive
  simp class this corpus guards against).
\<close>

declare gkr_chain_bad.simps [simp del]

lemma gkr_chain_bad_nil_empty [simp]:
  "Collect (gkr_chain_bad P A [] [] [] claims v) = {}"
  by (auto simp add: gkr_chain_bad.simps)

text \<open>
  One chain step costs at most \<open>2 s * dbnd / |'a|\<close> (a false incoming
  claim surviving the layer sumcheck, via AFP soundness) plus
  \<open>1 / |'a|\<close> (false carried evaluations colliding with the true next
  claim over the fresh carry challenge); the final layer has no carry
  continuation.  The bound telescopes by induction along the layer
  chain over the flat challenge tuple.
\<close>

lemma gkr_chain_bad_bound:
  fixes P :: "'a layer \<Rightarrow> nat \<Rightarrow> ('a list \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'p"
    and A :: "nat \<Rightarrow> 'a list \<Rightarrow> ('p, 'a, 'a, nat, 's) prover \<times> 's \<times> 'a \<times> 'a \<times> 'a"
    and dbnd :: "nat \<Rightarrow> nat"
      \<comment> \<open>the representative degree bound may depend on the layer width:
         a TOTAL-degree instance (the AFP mpoly one) has representatives
         of degree of order s, so a single constant bound over all widths
         would be undischargeable there; a max-per-variable
         instance discharges the constant function \<open>\<lambda>_. 4\<close>\<close>
  assumes wf: "gkr_chain_wf ss Ls bels"
    and repr: "\<And>L s claims b. layer_poly_repr (P L s claims b) L s claims b (dbnd s)"
    and false0: "v \<noteq> layer_claim_sum (hd Ls) claims (hd bels)"
  shows "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (chain_rlen ss)))
           {rs. gkr_chain_bad P A ss Ls bels claims v rs}
       \<le> (\<Sum>s\<leftarrow>ss. real (2 * s) * real (dbnd s) + 1) / real CARD('a)"
  using wf false0
proof (induction ss Ls bels arbitrary: claims v A rule: gkr_chain_wf.induct)
  case (2 s L b claims v A)
  obtain pr ps r0 tx0 ty0 where A00: "A 0 [] = (pr, ps, r0, tx0, ty0)"
    using prod_cases5 by blast
  define E1 where "E1 xs \<longleftrightarrow> sumcheck pr ps ({0, 1}, P L s claims b, v) r0
                               (zip (upt 0 (2 * s)) xs)" for xs :: "'a list"
  have gates: "\<forall>g \<in> set (layer_gates L). g_in1 g < 2 ^ s \<and> g_in2 g < 2 ^ s"
    using "2.prems"(1) by simp
  have f0: "v \<noteq> layer_claim_sum L claims b"
    using "2.prems"(2) by simp
  have ev: "{rs. gkr_chain_bad P A [s] [L] [b] claims v rs}
          = {rs. E1 (take (2 * s) rs)}"
    by (auto simp add: gkr_chain_bad.simps A00 E1_def)
  have "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (2 * s + 1)))
          {rs. E1 (take (2 * s) rs)}
      = measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (2 * s))) {xs. E1 xs}"
    by (rule prob_tuples_prefix)
  also have "\<dots> \<le> real (2 * s) * real (dbnd s) / real CARD('a)"
    unfolding E1_def by (rule layer_sumcheck_soundness[OF repr gates f0])
  finally have main: "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (2 * s + 1)))
          {rs. gkr_chain_bad P A [s] [L] [b] claims v rs}
      \<le> real (2 * s) * real (dbnd s) / real CARD('a)"
    by (simp add: ev)
  have pad: "real (2 * s) * real (dbnd s) / real CARD('a)
           \<le> (real (2 * s) * real (dbnd s) + 1) / real CARD('a)"
    by (intro divide_right_mono) simp_all
  show ?case using order_trans[OF main pad] by simp
next
  case (3 s s' ss L L' Ls b b' bs claims v A)
  let ?q = "real CARD('a)"
  let ?M = "chain_rlen (s' # ss)"
  let ?err' = "(\<Sum>t\<leftarrow>s' # ss. real (2 * t) * real (dbnd t) + 1) / ?q"
  obtain pr ps r0 tx0 ty0 where A00: "A 0 [] = (pr, ps, r0, tx0, ty0)"
    using prod_cases5 by blast
  define txf where "txf xs = fst (snd (snd (snd (A 0 xs))))" for xs
  define tyf where "tyf xs = snd (snd (snd (snd (A 0 xs))))" for xs
  have wfc: "(\<forall>g \<in> set (layer_gates L). g_in1 g < 2 ^ s \<and> g_in2 g < 2 ^ s) \<and>
             s = layer_width_bits L' \<and> b = layer_eval L' b' \<and>
             gkr_chain_wf (s' # ss) (L' # Ls) (b' # bs)"
    using "3.prems"(1) unfolding gkr_chain_wf.simps(3) .
  have gates: "\<forall>g \<in> set (layer_gates L). g_in1 g < 2 ^ s \<and> g_in2 g < 2 ^ s"
    and swb: "s = layer_width_bits L'"
    and beq: "b = layer_eval L' b'"
    and wf': "gkr_chain_wf (s' # ss) (L' # Ls) (b' # bs)"
    using wfc by blast+
  have f0: "v \<noteq> layer_claim_sum L claims b"
    using "3.prems"(2) by simp
  have q_pos: "0 < ?q" by (simp add: card_gt_0_iff)
  have err'_nonneg: "0 \<le> ?err'"
    by (intro divide_nonneg_nonneg sum_list_nonneg) auto

  \<comment> \<open>the three sub-events\<close>
  define S1 where "S1 = {rs :: 'a list.
     sumcheck pr ps ({0, 1}, P L s claims b, v) r0 (zip (upt 0 (2 * s)) (take (2 * s) rs))}"
  define TF where "TF rs \<longleftrightarrow>
     (txf (take (2 * s) rs) \<noteq> mle s ((!) b) (take s rs) \<or>
      tyf (take (2 * s) rs) \<noteq> mle s ((!) b) (take s (drop s rs)))" for rs :: "'a list"
  define NV where "NV rs =
     (txf (take (2 * s) rs) - const_mle L' (take s rs))
     + rs ! (2 * s) * (tyf (take (2 * s) rs) - const_mle L' (take s (drop s rs)))"
    for rs :: "'a list"
  define NC where "NC rs = [(take s rs, 1 :: 'a), (take s (drop s rs), rs ! (2 * s))]"
    for rs :: "'a list"
  define S2 where "S2 = {rs :: 'a list. TF rs \<and> NV rs = layer_claim_sum L' (NC rs) b'}"
  define S3 where "S3 = {rs :: 'a list. TF rs \<and> NV rs \<noteq> layer_claim_sum L' (NC rs) b' \<and>
     gkr_chain_bad P (\<lambda>j pfx. A (Suc j) (take (2 * s + 1) rs @ pfx)) (s' # ss) (L' # Ls)
       (b' # bs) (NC rs) (NV rs) (drop (2 * s + 1) rs)}"

  have unf: "gkr_chain_bad P A (s # s' # ss) (L # L' # Ls) (b # b' # bs) claims v rs
      \<longleftrightarrow> (rs \<in> S1 \<or>
           (TF rs \<and> gkr_chain_bad P (\<lambda>j pfx. A (Suc j) (take (2 * s + 1) rs @ pfx))
              (s' # ss) (L' # Ls) (b' # bs) (NC rs) (NV rs) (drop (2 * s + 1) rs)))"
    for rs :: "'a list"
    by (subst gkr_chain_bad.simps(1))
       (simp add: S1_def TF_def NV_def NC_def txf_def tyf_def A00 case_prod_beta)
  have subset: "{rs. gkr_chain_bad P A (s # s' # ss) (L # L' # Ls) (b # b' # bs) claims v rs}
              \<subseteq> S1 \<union> S2 \<union> S3"
  proof
    fix rs :: "'a list"
    assume "rs \<in> {rs. gkr_chain_bad P A (s # s' # ss) (L # L' # Ls) (b # b' # bs) claims v rs}"
    then have "rs \<in> S1 \<or>
           (TF rs \<and> gkr_chain_bad P (\<lambda>j pfx. A (Suc j) (take (2 * s + 1) rs @ pfx))
              (s' # ss) (L' # Ls) (b' # bs) (NC rs) (NV rs) (drop (2 * s + 1) rs))"
      using unf by blast
    then show "rs \<in> S1 \<union> S2 \<union> S3"
      by (auto simp add: S2_def S3_def)
  qed

  \<comment> \<open>bound the sumcheck sub-event\<close>
  have p1: "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (chain_rlen (s # s' # ss)))) S1
          \<le> real (2 * s) * real (dbnd s) / ?q"
  proof -
    have idx: "chain_rlen (s # s' # ss) = 2 * s + (1 + ?M)" by simp
    have "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (2 * s + (1 + ?M)))) S1
        = measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (2 * s)))
            {xs. sumcheck pr ps ({0, 1}, P L s claims b, v) r0 (zip (upt 0 (2 * s)) xs)}"
      unfolding S1_def
      by (rule prob_tuples_prefix)
    also have "\<dots> \<le> real (2 * s) * real (dbnd s) / ?q"
      by (rule layer_sumcheck_soundness[OF repr gates f0])
    finally show ?thesis by (simp add: idx)
  qed

  \<comment> \<open>bound the carry-collision sub-event\<close>
  have p2: "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (chain_rlen (s # s' # ss)))) S2
          \<le> 1 / ?q"
  proof -
    define E2 where "E2 pfx \<longleftrightarrow> TF pfx \<and> NV pfx = layer_claim_sum L' (NC pfx) b'"
      for pfx :: "'a list"
    have stable: "TF (take (2 * s + 1) rs) = TF rs \<and> NV (take (2 * s + 1) rs) = NV rs \<and>
                  NC (take (2 * s + 1) rs) = NC rs" for rs :: "'a list"
      by (simp add: TF_def NV_def NC_def take_take drop_take min_absorb1 min_absorb2)
    have st1: "TF (take (2 * s + 1) rs) = TF rs" for rs :: "'a list"
      using stable by blast
    have st2: "NV (take (2 * s + 1) rs) = NV rs" for rs :: "'a list"
      using stable by blast
    have st3: "NC (take (2 * s + 1) rs) = NC rs" for rs :: "'a list"
      using stable by blast
    have S2_pfx: "S2 = {rs. E2 (take (2 * s + 1) rs)}"
      unfolding S2_def E2_def by (simp only: st1 st2 st3)
    have idx: "chain_rlen (s # s' # ss) = (2 * s + 1) + ?M" by simp
    have "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) ((2 * s + 1) + ?M)))
            {rs. E2 (take (2 * s + 1) rs)}
        = measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (2 * s + 1))) {pfx. E2 pfx}"
      by (rule prob_tuples_prefix)
    also have "\<dots> \<le> 1 / ?q"
    proof -
      have split1: "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (2 * s + 1)))
              {pfx. E2 pfx}
          = (\<Sum>xs \<in> tuples (UNIV :: 'a set) (2 * s).
               measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) 1)) {ys. E2 (xs @ ys)})
            / ?q ^ (2 * s)"
        by (rule prob_tuples_split_seg)
      have per: "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) 1)) {ys. E2 (xs @ ys)}
               \<le> 1 / ?q" if xs: "xs \<in> tuples (UNIV :: 'a set) (2 * s)" for xs
      proof -
        from xs have len: "length xs = 2 * s" by auto
        have tk1: "take (2 * s) (xs @ ys) = xs" for ys :: "'a list"
          using len by simp
        have tk2: "take s (xs @ ys) = take s xs" for ys :: "'a list"
          using len by (simp add: take_append)
        have tk3: "take s (drop s (xs @ ys)) = drop s xs" for ys :: "'a list"
          using len by (simp add: drop_append take_append)
        have nth1: "(xs @ ys) ! (2 * s) = ys ! 0" for ys :: "'a list"
          using len by (simp add: nth_append)
        show ?thesis
        proof (cases "txf xs \<noteq> mle s ((!) b) (take s xs) \<or>
                      tyf xs \<noteq> mle s ((!) b) (drop s xs)")
          case True
          have ev2: "{ys :: 'a list. E2 (xs @ ys)}
                   = {ys. (txf xs - const_mle L' (take s xs))
                          + ys ! 0 * (tyf xs - const_mle L' (drop s xs))
                        = layer_claim_sum L' [(take s xs, 1), (drop s xs, ys ! 0)] b'}"
            using True
            by (auto simp add: E2_def TF_def NV_def NC_def tk1 tk2 tk3 nth1 len)
          have hyp: "txf xs \<noteq> mle (layer_width_bits L') ((!) (layer_eval L' b')) (take s xs) \<or>
                     tyf xs \<noteq> mle (layer_width_bits L') ((!) (layer_eval L' b')) (drop s xs)"
            using True swb beq by simp
          have "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) 1)) {ys. E2 (xs @ ys)}
              = measure_pmf.prob (pmf_of_set (UNIV :: 'a set))
                  {r. (txf xs - const_mle L' (take s xs))
                      + r * (tyf xs - const_mle L' (drop s xs))
                    = layer_claim_sum L' [(take s xs, 1), (drop s xs, r)] b'}"
            unfolding ev2
            by (rule prob_tuples_single[where Q = "\<lambda>r. (txf xs - const_mle L' (take s xs))
                      + r * (tyf xs - const_mle L' (drop s xs))
                    = layer_claim_sum L' [(take s xs, 1), (drop s xs, r)] b'"])
          also have "\<dots> \<le> 1 / ?q"
            by (rule carried_claim_carry_sound[OF hyp])
          finally show ?thesis .
        next
          case False
          then have "{ys :: 'a list. E2 (xs @ ys)} = {}"
            by (auto simp add: E2_def TF_def tk1 tk2 tk3 len)
          then show ?thesis using q_pos by simp
        qed
      qed
      have qnz: "?q ^ (2 * s) \<noteq> 0" using q_pos by simp
      have sumb: "(\<Sum>xs \<in> tuples (UNIV :: 'a set) (2 * s).
               measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) 1)) {ys. E2 (xs @ ys)})
          \<le> ?q ^ (2 * s) * (1 / ?q)"
      proof -
        have "(\<Sum>xs \<in> tuples (UNIV :: 'a set) (2 * s).
                 measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) 1)) {ys. E2 (xs @ ys)})
            \<le> (\<Sum>xs \<in> tuples (UNIV :: 'a set) (2 * s). 1 / ?q)"
          by (rule sum_mono) (rule per)
        then show ?thesis by (simp add: card_tuples_UNIV)
      qed
      have qp2: "0 \<le> ?q ^ (2 * s)" by (intro zero_le_power) simp
      have "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (2 * s + 1))) {pfx. E2 pfx}
          \<le> (?q ^ (2 * s) * (1 / ?q)) / ?q ^ (2 * s)"
        unfolding split1 by (rule divide_right_mono[OF sumb qp2])
      also have "\<dots> = 1 / ?q"
        using qnz by simp
      finally show ?thesis .
    qed
    finally show ?thesis using S2_pfx idx by simp
  qed

  \<comment> \<open>bound the continuation sub-event by the induction hypothesis\<close>
  have p3: "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (chain_rlen (s # s' # ss)))) S3
          \<le> ?err'"
  proof -
    have idx: "chain_rlen (s # s' # ss) = (2 * s + 1) + ?M" by simp
    have split1: "measure_pmf.prob
            (pmf_of_set (tuples (UNIV :: 'a set) ((2 * s + 1) + ?M))) S3
        = (\<Sum>seg \<in> tuples (UNIV :: 'a set) (2 * s + 1).
             measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) ?M))
               {rest. seg @ rest \<in> S3})
          / ?q ^ (2 * s + 1)"
      using prob_tuples_split_seg[where E = "\<lambda>zs. zs \<in> S3" and k = "2 * s + 1"
              and m = "chain_rlen (s' # ss)"] by simp
    have per: "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) ?M))
                 {rest. seg @ rest \<in> S3} \<le> ?err'"
      if seg: "seg \<in> tuples (UNIV :: 'a set) (2 * s + 1)" for seg
    proof -
      from seg have len: "length seg = 2 * s + 1" by auto
      have tkA: "take (2 * s) (seg @ rest) = take (2 * s) seg" for rest :: "'a list"
        using len by (simp add: take_append)
      have tkB: "take s (seg @ rest) = take s seg" for rest :: "'a list"
        using len by (simp add: take_append)
      have tkC: "take s (drop s (seg @ rest)) = take s (drop s seg)" for rest :: "'a list"
        using len by (simp add: drop_append take_append)
      have nthA: "(seg @ rest) ! (2 * s) = seg ! (2 * s)" for rest :: "'a list"
        using len by (simp add: nth_append)
      have tkF: "take (2 * s + 1) (seg @ rest) = seg" for rest :: "'a list"
        using len by simp
      have drF: "drop (2 * s + 1) (seg @ rest) = rest" for rest :: "'a list"
        using len by simp
      have stable: "TF (seg @ rest) = TF seg \<and> NV (seg @ rest) = NV seg \<and>
                    NC (seg @ rest) = NC seg" for rest :: "'a list"
        by (simp add: TF_def NV_def NC_def tkA tkB tkC nthA len)
      show ?thesis
      proof (cases "TF seg \<and> NV seg \<noteq> layer_claim_sum L' (NC seg) b'")
        case True
        have sub: "{rest. seg @ rest \<in> S3}
                 \<subseteq> {rest. gkr_chain_bad P (\<lambda>j pfx. A (Suc j) (seg @ pfx)) (s' # ss)
                            (L' # Ls) (b' # bs) (NC seg) (NV seg) rest}"
          by (auto simp add: S3_def stable tkF drF len)
        have "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) ?M))
                {rest. seg @ rest \<in> S3}
            \<le> measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) ?M))
                {rest. gkr_chain_bad P (\<lambda>j pfx. A (Suc j) (seg @ pfx)) (s' # ss)
                         (L' # Ls) (b' # bs) (NC seg) (NV seg) rest}"
          using sub by (intro prob_mono) auto
        also have "\<dots> \<le> ?err'"
          using True by (intro "3.IH"[OF wf']) simp
        finally show ?thesis .
      next
        case False
        then have "{rest. seg @ rest \<in> S3} = {}"
          by (auto simp add: S3_def stable)
        then show ?thesis using err'_nonneg by simp
      qed
    qed
    have qnz: "?q ^ (2 * s + 1) \<noteq> 0" using q_pos by simp
    have sumb: "(\<Sum>seg \<in> tuples (UNIV :: 'a set) (2 * s + 1).
             measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) ?M))
               {rest. seg @ rest \<in> S3})
        \<le> ?q ^ (2 * s + 1) * ?err'"
    proof -
      have "(\<Sum>seg \<in> tuples (UNIV :: 'a set) (2 * s + 1).
               measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) ?M))
                 {rest. seg @ rest \<in> S3})
          \<le> (\<Sum>seg \<in> tuples (UNIV :: 'a set) (2 * s + 1). ?err')"
        by (rule sum_mono) (rule per)
      then show ?thesis by (simp add: card_tuples_UNIV)
    qed
    have qp3: "0 \<le> ?q ^ (2 * s + 1)" by (intro zero_le_power) simp
    have "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set)
            ((2 * s + 1) + ?M))) S3
        \<le> (?q ^ (2 * s + 1) * ?err') / ?q ^ (2 * s + 1)"
      unfolding split1 by (rule divide_right_mono[OF sumb qp3])
    also have "\<dots> = ?err'"
      using qnz by simp
    finally show ?thesis by (simp add: idx)
  qed

  \<comment> \<open>assemble\<close>
  have u2: "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set)
              (chain_rlen (s # s' # ss)))) (S1 \<union> S2)
          \<le> measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set)
              (chain_rlen (s # s' # ss)))) S1
          + measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set)
              (chain_rlen (s # s' # ss)))) S2"
    by (rule measure_Un_le) simp_all
  have "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (chain_rlen (s # s' # ss))))
          {rs. gkr_chain_bad P A (s # s' # ss) (L # L' # Ls) (b # b' # bs) claims v rs}
      \<le> measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (chain_rlen (s # s' # ss))))
          (S1 \<union> S2 \<union> S3)"
    using subset by (intro prob_mono) auto
  also have "\<dots> \<le> measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set)
                    (chain_rlen (s # s' # ss)))) (S1 \<union> S2)
                + measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set)
                    (chain_rlen (s # s' # ss)))) S3"
    by (rule measure_Un_le) simp_all
  also have "\<dots> \<le> (measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set)
                     (chain_rlen (s # s' # ss)))) S1
                 + measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set)
                     (chain_rlen (s # s' # ss)))) S2)
                + measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set)
                     (chain_rlen (s # s' # ss)))) S3"
    by (rule add_right_mono[OF u2])
  also have "\<dots> \<le> (real (2 * s) * real (dbnd s) / ?q + 1 / ?q) + ?err'"
    by (intro add_mono p1 p2 p3)
  also have "\<dots> = (\<Sum>t\<leftarrow>s # s' # ss. real (2 * t) * real (dbnd t) + 1) / ?q"
    by (simp add: add_divide_distrib)
  finally show ?case .
qed (auto simp add: gkr_chain_bad.simps measure_empty)

text \<open>
  Theorem B, assembled (target name of the recorded B3 plan): if the
  claimed output table differs anywhere on the output cube from the true
  circuit output, then for ANY adversary the chain bad event - seeded by
  the verifier-computed claimed-output MLE at the random \<open>z_0\<close> tuple
  (reduce.rs: \<open>m0\<close>), threaded through every layer reduction and carry -
  has probability at most

    \<open>(s_out + sum over layers of (2 s_i dbnd + 1)) / |'a|\<close>

  over the flat verifier randomness \<open>z_0 @ per-layer challenges\<close>.  The
  output-layer summand is the multilinear Schwartz-Zippel seed
  (\<open>mle_agree_prob\<close>); each layer contributes its sumcheck soundness plus
  one carry collision.
\<close>

theorem gkr_assembly_soundness:
  fixes P :: "'a layer \<Rightarrow> nat \<Rightarrow> ('a list \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'p"
    and A :: "nat \<Rightarrow> 'a list \<Rightarrow> ('p, 'a, 'a, nat, 's) prover \<times> 's \<times> 'a \<times> 'a \<times> 'a"
    and outs :: "nat \<Rightarrow> 'a"
    and dbnd :: "nat \<Rightarrow> nat"
  assumes wf: "gkr_chain_wf (s0 # ss) (L0 # Ls) (b0 # bs)"
    and repr: "\<And>L s claims b. layer_poly_repr (P L s claims b) L s claims b (dbnd s)"
    and outs_ne: "\<exists>idx < 2 ^ layer_width_bits L0. outs idx \<noteq> layer_eval L0 b0 ! idx"
  shows "measure_pmf.prob
           (pmf_of_set (tuples (UNIV :: 'a set)
              (layer_width_bits L0 + chain_rlen (s0 # ss))))
           {rs. gkr_chain_bad P (\<lambda>j pfx. A j (take (layer_width_bits L0) rs @ pfx))
                  (s0 # ss) (L0 # Ls) (b0 # bs)
                  [(take (layer_width_bits L0) rs, 1)]
                  (mle (layer_width_bits L0) outs (take (layer_width_bits L0) rs)
                   - const_mle L0 (take (layer_width_bits L0) rs))
                  (drop (layer_width_bits L0) rs)}
       \<le> (real (layer_width_bits L0)
           + (\<Sum>s\<leftarrow>s0 # ss. real (2 * s) * real (dbnd s) + 1)) / real CARD('a)"
proof -
  define n0 where "n0 = layer_width_bits L0"
  have outs_ne': "\<exists>idx < 2 ^ n0. outs idx \<noteq> layer_eval L0 b0 ! idx"
    using outs_ne by (simp add: n0_def)
  let ?q = "real CARD('a)"
  let ?N = "n0 + chain_rlen (s0 # ss)"
  let ?err = "(\<Sum>s\<leftarrow>s0 # ss. real (2 * s) * real (dbnd s) + 1) / ?q"
  define ES where "ES z0 \<longleftrightarrow> mle n0 outs z0 = mle n0 ((!) (layer_eval L0 b0)) z0"
    for z0 :: "'a list"
  define SEED where "SEED = {rs :: 'a list. ES (take n0 rs)}"
  define REST where "REST = {rs :: 'a list.
     mle n0 outs (take n0 rs) - const_mle L0 (take n0 rs)
       \<noteq> layer_claim_sum L0 [(take n0 rs, 1)] b0 \<and>
     gkr_chain_bad P (\<lambda>j pfx. A j (take n0 rs @ pfx)) (s0 # ss) (L0 # Ls) (b0 # bs)
       [(take n0 rs, 1)]
       (mle n0 outs (take n0 rs) - const_mle L0 (take n0 rs)) (drop n0 rs)}"
  have q_pos: "0 < ?q" by (simp add: card_gt_0_iff)
  have err_nonneg: "0 \<le> ?err"
    by (intro divide_nonneg_nonneg sum_list_nonneg) auto

  have claim_sum1: "layer_claim_sum L0 [(z0, 1)] b0
      = mle n0 ((!) (layer_eval L0 b0)) z0 - const_mle L0 z0" for z0 :: "'a list"
    by (simp add: layer_claim_sum_def n0_def)

  have subset: "{rs. gkr_chain_bad P (\<lambda>j pfx. A j (take n0 rs @ pfx))
                  (s0 # ss) (L0 # Ls) (b0 # bs) [(take n0 rs, 1)]
                  (mle n0 outs (take n0 rs) - const_mle L0 (take n0 rs)) (drop n0 rs)}
              \<subseteq> SEED \<union> REST"
  proof
    fix rs :: "'a list"
    assume rs: "rs \<in> {rs. gkr_chain_bad P (\<lambda>j pfx. A j (take n0 rs @ pfx))
                  (s0 # ss) (L0 # Ls) (b0 # bs) [(take n0 rs, 1)]
                  (mle n0 outs (take n0 rs) - const_mle L0 (take n0 rs)) (drop n0 rs)}"
    show "rs \<in> SEED \<union> REST"
    proof (cases "mle n0 outs (take n0 rs) = mle n0 ((!) (layer_eval L0 b0)) (take n0 rs)")
      case True
      then show ?thesis by (simp add: SEED_def ES_def)
    next
      case False
      then have "mle n0 outs (take n0 rs) - const_mle L0 (take n0 rs)
               \<noteq> layer_claim_sum L0 [(take n0 rs, 1)] b0"
        by (simp add: claim_sum1)
      then show ?thesis using rs by (auto simp add: REST_def)
    qed
  qed

  have pSEED: "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) ?N)) SEED
             \<le> real n0 / ?q"
  proof -
    have "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set)
            (n0 + chain_rlen (s0 # ss)))) SEED
        = measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) n0)) {z0. ES z0}"
      unfolding SEED_def by (rule prob_tuples_prefix)
    also have "\<dots> \<le> real n0 / ?q"
      unfolding ES_def by (rule mle_agree_prob[OF outs_ne'])
    finally show ?thesis .
  qed

  have pREST: "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) ?N)) REST \<le> ?err"
  proof -
    have split1: "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set)
            (n0 + chain_rlen (s0 # ss)))) REST
        = (\<Sum>z0 \<in> tuples (UNIV :: 'a set) n0.
             measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (chain_rlen (s0 # ss))))
               {rest. z0 @ rest \<in> REST})
          / ?q ^ n0"
      using prob_tuples_split_seg[where E = "\<lambda>zs. zs \<in> REST" and k = n0
              and m = "chain_rlen (s0 # ss)"] by simp
    have per: "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (chain_rlen (s0 # ss))))
                 {rest. z0 @ rest \<in> REST} \<le> ?err"
      if z0: "z0 \<in> tuples (UNIV :: 'a set) n0" for z0
    proof -
      from z0 have len: "length z0 = n0" by auto
      have tk: "take n0 (z0 @ rest) = z0" for rest :: "'a list"
        using len by simp
      have dr: "drop n0 (z0 @ rest) = rest" for rest :: "'a list"
        using len by simp
      show ?thesis
      proof (cases "mle n0 outs z0 - const_mle L0 z0
                    \<noteq> layer_claim_sum L0 [(z0, 1)] b0")
        case True
        have sub: "{rest. z0 @ rest \<in> REST}
                 \<subseteq> {rest. gkr_chain_bad P (\<lambda>j pfx. A j (z0 @ pfx)) (s0 # ss)
                            (L0 # Ls) (b0 # bs) [(z0, 1)]
                            (mle n0 outs z0 - const_mle L0 z0) rest}"
          by (auto simp add: REST_def tk dr len)
        have "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set)
                (chain_rlen (s0 # ss)))) {rest. z0 @ rest \<in> REST}
            \<le> measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set)
                (chain_rlen (s0 # ss))))
                {rest. gkr_chain_bad P (\<lambda>j pfx. A j (z0 @ pfx)) (s0 # ss)
                         (L0 # Ls) (b0 # bs) [(z0, 1)]
                         (mle n0 outs z0 - const_mle L0 z0) rest}"
          using sub by (intro prob_mono) auto
        also have "\<dots> \<le> ?err"
          using True by (intro gkr_chain_bad_bound[OF wf repr]) simp
        finally show ?thesis .
      next
        case False
        then have "{rest. z0 @ rest \<in> REST} = {}"
          by (auto simp add: REST_def tk len)
        then show ?thesis using err_nonneg by simp
      qed
    qed
    have qnz: "?q ^ n0 \<noteq> 0" using q_pos by simp
    have sumb: "(\<Sum>z0 \<in> tuples (UNIV :: 'a set) n0.
             measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (chain_rlen (s0 # ss))))
               {rest. z0 @ rest \<in> REST})
        \<le> ?q ^ n0 * ?err"
    proof -
      have "(\<Sum>z0 \<in> tuples (UNIV :: 'a set) n0.
               measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) (chain_rlen (s0 # ss))))
                 {rest. z0 @ rest \<in> REST})
          \<le> (\<Sum>z0 \<in> tuples (UNIV :: 'a set) n0. ?err)"
        by (rule sum_mono) (rule per)
      then show ?thesis by (simp add: card_tuples_UNIV)
    qed
    have qpn: "0 \<le> ?q ^ n0" by (intro zero_le_power) simp
    have "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set)
            (n0 + chain_rlen (s0 # ss)))) REST
        \<le> (?q ^ n0 * ?err) / ?q ^ n0"
      unfolding split1 by (rule divide_right_mono[OF sumb qpn])
    also have "\<dots> = ?err"
      using qnz by simp
    finally show ?thesis .
  qed

  have "measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) ?N))
          {rs. gkr_chain_bad P (\<lambda>j pfx. A j (take n0 rs @ pfx))
                 (s0 # ss) (L0 # Ls) (b0 # bs) [(take n0 rs, 1)]
                 (mle n0 outs (take n0 rs) - const_mle L0 (take n0 rs)) (drop n0 rs)}
      \<le> measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) ?N)) (SEED \<union> REST)"
    using subset by (intro prob_mono) auto
  also have "\<dots> \<le> measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) ?N)) SEED
                + measure_pmf.prob (pmf_of_set (tuples (UNIV :: 'a set) ?N)) REST"
    by (rule measure_Un_le) simp_all
  also have "\<dots> \<le> real n0 / ?q + ?err"
    by (intro add_mono pSEED pREST)
  also have "\<dots> = (real n0 + (\<Sum>s\<leftarrow>s0 # ss. real (2 * s) * real (dbnd s) + 1)) / ?q"
    by (simp add: add_divide_distrib)
  finally show ?thesis by (simp add: n0_def)
qed

corollary gkr_assembly_soundness_deg4:
  fixes P :: "'a layer \<Rightarrow> nat \<Rightarrow> ('a list \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'p"
    and A :: "nat \<Rightarrow> 'a list \<Rightarrow> ('p, 'a, 'a, nat, 's) prover \<times> 's \<times> 'a \<times> 'a \<times> 'a"
    and outs :: "nat \<Rightarrow> 'a"
  assumes "gkr_chain_wf (s0 # ss) (L0 # Ls) (b0 # bs)"
    and "\<And>L s claims b. layer_poly_repr (P L s claims b) L s claims b 4"
    and "\<exists>idx < 2 ^ layer_width_bits L0. outs idx \<noteq> layer_eval L0 b0 ! idx"
  shows "measure_pmf.prob
           (pmf_of_set (tuples (UNIV :: 'a set)
              (layer_width_bits L0 + chain_rlen (s0 # ss))))
           {rs. gkr_chain_bad P (\<lambda>j pfx. A j (take (layer_width_bits L0) rs @ pfx))
                  (s0 # ss) (L0 # Ls) (b0 # bs)
                  [(take (layer_width_bits L0) rs, 1)]
                  (mle (layer_width_bits L0) outs (take (layer_width_bits L0) rs)
                   - const_mle L0 (take (layer_width_bits L0) rs))
                  (drop (layer_width_bits L0) rs)}
       \<le> (real (layer_width_bits L0)
           + (\<Sum>s\<leftarrow>s0 # ss. real (2 * s) * 4 + 1)) / real CARD('a)"
proof -
  have r: "\<And>L s claims b. layer_poly_repr (P L s claims b) L s claims b ((\<lambda>_. 4) s)"
    using assms(2) by simp
  show ?thesis
    using gkr_assembly_soundness[OF assms(1) r assms(3)] by simp
qed

end

end
