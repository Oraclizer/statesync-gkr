(*
  Title:   Multilinear_Extension.thy
  Session: GKR_Protocol (generic layer)

  Multilinear extensions of value tables over the boolean hypercube,
  in the exact convention of the Rust helpers (crate `ssgkr-protocol`,
  `mle.rs`, frozen with seal point S-2):

  - a POINT is a field-element list, one entry per variable;
  - variable 0 is the MOST significant index bit: for an n-variable
    point and index idx < 2^n, variable j carries bit (idx >> (n-1-j)) & 1;
  - eq_pi point idx  ~  eq_point_index (the multilinear Lagrange weight);
  - mle n f point = sum over idx < 2^n of eq_pi point idx * f idx
    (Rust pins this shape via the `mle_eval_as_eq_combination` test);
  - beta point = eq_pi point 0 = prod_j (1 - point_j)  ~  beta_eval
    (the all-zero indicator used to lift unary sumcheck terms).

  These definitions and the boolean-point lemmas below are the shared
  foundation of the wiring-predicate MLEs (Wiring_MLE) and the GKR layer
  identity (GKR_Assembly).
*)

theory Multilinear_Extension
  imports Main
begin

section \<open>Index bits (variable 0 = MSB)\<close>

text \<open>
  \<open>bit_at n idx j\<close>: the bit carried by variable \<open>j\<close> of an \<open>n\<close>-variable
  index, i.e. bit \<open>n - 1 - j\<close> of \<open>idx\<close> (Rust: \<open>(idx >> (n-1-j)) & 1\<close>).
\<close>

definition bit_at :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "bit_at n idx j \<longleftrightarrow> bit idx (n - 1 - j)"

lemma bit_at_iff_odd_div: "bit_at n idx j \<longleftrightarrow> odd (idx div 2 ^ (n - 1 - j))"
  by (simp add: bit_at_def bit_iff_odd)

text \<open>The boolean point of an index: entry \<open>j\<close> is bit \<open>j\<close> (MSB first).\<close>

definition bool_point :: "nat \<Rightarrow> nat \<Rightarrow> 'f::comm_ring_1 list" where
  "bool_point n idx = map (\<lambda>j. if bit_at n idx j then 1 else 0) [0 ..< n]"

lemma length_bool_point [simp]: "length (bool_point n idx) = n"
  by (simp add: bool_point_def)

lemma bool_point_nth:
  "j < n \<Longrightarrow> (bool_point n idx :: 'f::comm_ring_1 list) ! j =
               (if bit_at n idx j then 1 else 0)"
  by (simp add: bool_point_def)

section \<open>The Lagrange basis weight (eq)\<close>

text \<open>
  \<open>eq_pi point idx\<close>: product over variables of \<open>point!j\<close> where bit \<open>j\<close> of
  \<open>idx\<close> is one, and \<open>1 - point!j\<close> where it is zero (Rust:
  \<open>eq_point_index\<close>).
\<close>

definition eq_pi :: "'f::comm_ring_1 list \<Rightarrow> nat \<Rightarrow> 'f" where
  "eq_pi pt idx =
     (\<Prod>j < length pt. if bit_at (length pt) idx j then pt ! j else 1 - pt ! j)"

lemma eq_pi_nil [simp]: "eq_pi [] idx = 1"
  by (simp add: eq_pi_def)

text \<open>First-element shift for products over an initial segment.\<close>

lemma prod_lessThan_Suc_shift:
  fixes f :: "nat \<Rightarrow> 'f::comm_monoid_mult"
  shows "(\<Prod>j < Suc n. f j) = f 0 * (\<Prod>j < n. f (Suc j))"
  by (induction n) (simp_all add: mult.assoc)

section \<open>Boolean-point facts\<close>

text \<open>An index below \<open>2^n\<close> is determined by its \<open>n\<close> variable bits.\<close>

lemma bit_at_complete:
  assumes "idx < 2 ^ n" "idx' < 2 ^ n"
      and "\<And>j. j < n \<Longrightarrow> bit_at n idx j = bit_at n idx' j"
  shows "idx = idx'"
proof (rule bit_eqI)
  fix i :: nat
  show "bit idx i = bit idx' i"
  proof (cases "i < n")
    case True
    then have "bit_at n idx (n - 1 - i) = bit_at n idx' (n - 1 - i)"
      using assms(3) by simp
    with True show ?thesis by (simp add: bit_at_def)
  next
    case False
    have high: "\<not> bit m i" if "m < 2 ^ n" for m :: nat
    proof -
      have "(2 :: nat) ^ n \<le> 2 ^ i"
        using False by (simp add: power_increasing)
      then have "m < 2 ^ i" using that by linarith
      then show "\<not> bit m i"
        by (simp add: bit_iff_odd div_less)
    qed
    show ?thesis using high assms(1,2) by simp
  qed
qed

text \<open>On boolean points, \<open>eq_pi\<close> is the Kronecker delta (Rust test
  \<open>eq_is_kronecker_on_boolean_points\<close>).\<close>

lemma eq_pi_bool_point:
  assumes "idx < 2 ^ n" "idx' < 2 ^ n"
  shows "eq_pi (bool_point n idx :: 'f::comm_ring_1 list) idx' =
           (if idx = idx' then 1 else 0)"
proof (cases "idx = idx'")
  case True
  have "(if bit_at n idx' j then (bool_point n idx :: 'f list) ! j
         else 1 - bool_point n idx ! j) = 1" if "j < n" for j
    using that True by (simp add: bool_point_nth)
  then show ?thesis
    unfolding eq_pi_def by (simp add: True)
next
  case False
  then obtain j where jn: "j < n" and neq: "bit_at n idx j \<noteq> bit_at n idx' j"
    using bit_at_complete assms by blast
  have zero_factor:
    "(if bit_at n idx' j then (bool_point n idx :: 'f list) ! j
      else 1 - bool_point n idx ! j) = 0"
    using neq jn by (simp add: bool_point_nth split: if_splits)
  have "eq_pi (bool_point n idx :: 'f list) idx' =
        (\<Prod>k < n. if bit_at n idx' k then (bool_point n idx :: 'f list) ! k
                  else 1 - bool_point n idx ! k)"
    by (simp add: eq_pi_def)
  also have "\<dots> = 0"
  proof (rule prod_zero)
    show "finite {..< n}" by simp
    show "\<exists>a\<in>{..< n}. (if bit_at n idx' a then (bool_point n idx :: 'f list) ! a
                        else 1 - bool_point n idx ! a) = 0"
      using jn zero_factor by (intro bexI[of _ j]) auto
  qed
  finally show ?thesis using False by simp
qed

subsection \<open>Head/tail decomposition of the weight\<close>

text \<open>
  Splitting one variable off the front: the head variable carries the top
  bit, the tail variables carry the low bits.  These two lemmas drive every
  induction over the point list.
\<close>

lemma bit_at_head_lo: "idx < 2 ^ n \<Longrightarrow> \<not> bit_at (Suc n) idx 0"
  by (simp add: bit_at_def bit_iff_odd div_less)

lemma bit_at_head_hi: "idx < 2 ^ n \<Longrightarrow> bit_at (Suc n) (idx + 2 ^ n) 0"
  by (simp add: bit_at_def bit_iff_odd div_add_self2 div_less)

lemma bit_at_tail_lo:
  assumes "j < n"
  shows "bit_at (Suc n) idx (Suc j) = bit_at n idx j"
  using assms by (simp add: bit_at_def)

lemma bit_at_tail_hi:
  assumes "idx < 2 ^ n" "j < n"
  shows "bit_at (Suc n) (idx + 2 ^ n) (Suc j) = bit_at n idx j"
proof -
  have i_lt: "n - 1 - j < n" using assms(2) by simp
  have "bit (idx + 2 ^ n) (n - 1 - j) = bit idx (n - 1 - j)"
  proof -
    have dvd: "(2 :: nat) ^ (n - 1 - j) dvd 2 ^ n"
      using i_lt by (simp add: le_imp_power_dvd)
    have "(idx + 2 ^ n) div 2 ^ (n - 1 - j) =
          idx div 2 ^ (n - 1 - j) + 2 ^ n div 2 ^ (n - 1 - j)"
      using dvd by (simp add: div_plus_div_distrib_dvd_right)
    moreover have "(2 :: nat) ^ n div 2 ^ (n - 1 - j) = 2 ^ (n - (n - 1 - j))"
    proof -
      have exp_eq: "(n - 1 - j) + (n - (n - 1 - j)) = n"
        using i_lt by arith
      have "(2 :: nat) ^ n = 2 ^ (n - 1 - j) * 2 ^ (n - (n - 1 - j))"
        by (metis exp_eq power_add)
      then show ?thesis by simp
    qed
    moreover have "even ((2 :: nat) ^ (n - (n - 1 - j)))"
      using i_lt by simp
    ultimately show ?thesis
      by (simp add: bit_iff_odd)
  qed
  then show ?thesis
    using assms(2) by (simp add: bit_at_def)
qed

lemma eq_pi_cons_lo:
  fixes p :: "'f::comm_ring_1"
  assumes "idx < 2 ^ length ps"
  shows "eq_pi (p # ps) idx = (1 - p) * eq_pi ps idx"
proof -
  let ?n = "length ps"
  have "eq_pi (p # ps) idx =
        (\<Prod>j < Suc ?n. if bit_at (Suc ?n) idx j then (p # ps) ! j else 1 - (p # ps) ! j)"
    by (simp add: eq_pi_def)
  also have "\<dots> = (if bit_at (Suc ?n) idx 0 then p else 1 - p) *
        (\<Prod>j < ?n. if bit_at (Suc ?n) idx (Suc j) then ps ! j else 1 - ps ! j)"
    by (simp only: prod_lessThan_Suc_shift nth_Cons_0 nth_Cons_Suc)
  also have "\<dots> = (1 - p) *
        (\<Prod>j < ?n. if bit_at ?n idx j then ps ! j else 1 - ps ! j)"
  proof -
    have head: "(if bit_at (Suc ?n) idx 0 then p else 1 - p) = 1 - p"
      using bit_at_head_lo[OF assms] by simp
    have tail: "(\<Prod>j < ?n. if bit_at (Suc ?n) idx (Suc j) then ps ! j else 1 - ps ! j) =
                (\<Prod>j < ?n. if bit_at ?n idx j then ps ! j else 1 - ps ! j)"
      by (intro prod.cong refl) (simp add: bit_at_tail_lo)
    show ?thesis by (simp only: head tail)
  qed
  finally show ?thesis by (simp add: eq_pi_def)
qed

lemma eq_pi_cons_hi:
  fixes p :: "'f::comm_ring_1"
  assumes "idx < 2 ^ length ps"
  shows "eq_pi (p # ps) (idx + 2 ^ length ps) = p * eq_pi ps idx"
proof -
  let ?n = "length ps"
  have "eq_pi (p # ps) (idx + 2 ^ ?n) =
        (\<Prod>j < Suc ?n. if bit_at (Suc ?n) (idx + 2 ^ ?n) j
                       then (p # ps) ! j else 1 - (p # ps) ! j)"
    by (simp add: eq_pi_def)
  also have "\<dots> = (if bit_at (Suc ?n) (idx + 2 ^ ?n) 0 then p else 1 - p) *
        (\<Prod>j < ?n. if bit_at (Suc ?n) (idx + 2 ^ ?n) (Suc j) then ps ! j else 1 - ps ! j)"
    by (simp only: prod_lessThan_Suc_shift nth_Cons_0 nth_Cons_Suc)
  also have "\<dots> = p * (\<Prod>j < ?n. if bit_at ?n idx j then ps ! j else 1 - ps ! j)"
  proof -
    have head: "(if bit_at (Suc ?n) (idx + 2 ^ ?n) 0 then p else 1 - p) = p"
      using bit_at_head_hi[OF assms] by simp
    have tail: "(\<Prod>j < ?n. if bit_at (Suc ?n) (idx + 2 ^ ?n) (Suc j)
                           then ps ! j else 1 - ps ! j) =
                (\<Prod>j < ?n. if bit_at ?n idx j then ps ! j else 1 - ps ! j)"
      by (intro prod.cong refl) (simp add: bit_at_tail_hi[OF assms])
    show ?thesis by (simp only: head tail)
  qed
  finally show ?thesis by (simp add: eq_pi_def)
qed

subsection \<open>Partition of unity\<close>

text \<open>The Lagrange weights sum to one at every point (the \<open>sum_y beta\<close>
  lifting in the layer sumcheck rests on this).\<close>

lemma sum_eq_pi_one:
  fixes pt :: "'f::comm_ring_1 list"
  shows "(\<Sum>idx < 2 ^ length pt. eq_pi pt idx) = 1"
proof (induction pt)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  let ?n = "length ps"
  have split: "{..< (2 :: nat) ^ Suc ?n} = {..< 2 ^ ?n} \<union> (\<lambda>i. i + 2 ^ ?n) ` {..< 2 ^ ?n}"
  proof
    show "{..< (2 :: nat) ^ Suc ?n} \<subseteq> {..< 2 ^ ?n} \<union> (\<lambda>i. i + 2 ^ ?n) ` {..< 2 ^ ?n}"
    proof
      fix x assume "x \<in> {..< (2 :: nat) ^ Suc ?n}"
      then have "x < 2 * 2 ^ ?n" by simp
      then show "x \<in> {..< 2 ^ ?n} \<union> (\<lambda>i. i + 2 ^ ?n) ` {..< 2 ^ ?n}"
      proof (cases "x < 2 ^ ?n")
        case False
        then have "x - 2 ^ ?n < 2 ^ ?n" and "x = (x - 2 ^ ?n) + 2 ^ ?n"
          using \<open>x < 2 * 2 ^ ?n\<close> by simp_all
        then show ?thesis by force
      qed simp
    qed
  next
    show "{..< 2 ^ ?n} \<union> (\<lambda>i. i + 2 ^ ?n) ` {..< 2 ^ ?n} \<subseteq> {..< (2 :: nat) ^ Suc ?n}"
      by auto
  qed
  have inj: "inj_on (\<lambda>i. i + (2 :: nat) ^ ?n) {..< 2 ^ ?n}"
    by (simp add: inj_on_def)
  have disj: "{..< (2 :: nat) ^ ?n} \<inter> (\<lambda>i. i + 2 ^ ?n) ` {..< 2 ^ ?n} = {}"
    by auto
  have "(\<Sum>idx < 2 ^ length (p # ps). eq_pi (p # ps) idx) =
        (\<Sum>idx \<in> {..< (2 :: nat) ^ Suc ?n}. eq_pi (p # ps) idx)"
    by simp
  also have "\<dots> = (\<Sum>idx \<in> {..< 2 ^ ?n} \<union> (\<lambda>i. i + 2 ^ ?n) ` {..< 2 ^ ?n}. eq_pi (p # ps) idx)"
    by (simp only: split)
  also have "\<dots> = (\<Sum>idx < 2 ^ ?n. eq_pi (p # ps) idx) +
                  (\<Sum>idx < 2 ^ ?n. eq_pi (p # ps) (idx + 2 ^ ?n))"
    by (simp add: sum.union_disjoint disj inj sum.reindex)
  also have "\<dots> = (1 - p) * (\<Sum>idx < 2 ^ ?n. eq_pi ps idx) +
                  p * (\<Sum>idx < 2 ^ ?n. eq_pi ps idx)"
    by (simp add: eq_pi_cons_lo eq_pi_cons_hi sum_distrib_left)
  also have "\<dots> = 1" using Cons.IH by (simp add: algebra_simps)
  finally show ?case .
qed

section \<open>Multilinear extension of a value table\<close>

text \<open>
  \<open>mle n f pt\<close>: the multilinear extension of the table \<open>f\<close> (indexed by
  \<open>{0 ..< 2^n}\<close>) evaluated at \<open>pt\<close>.  Shape pinned by the Rust test
  \<open>mle_eval_as_eq_combination\<close>: MLE(v)(r) = sum over idx of v[idx] * eq(r, idx).
\<close>

definition mle :: "nat \<Rightarrow> (nat \<Rightarrow> 'f) \<Rightarrow> 'f::comm_ring_1 list \<Rightarrow> 'f" where
  "mle n f pt = (\<Sum>idx < 2 ^ n. eq_pi pt idx * f idx)"

text \<open>On boolean points the MLE agrees with the table (Rust test
  \<open>mle_eval_matches_table_on_hypercube\<close>).\<close>

lemma mle_bool_point:
  assumes "idx < 2 ^ n"
  shows "mle n f (bool_point n idx :: 'f::comm_ring_1 list) = f idx"
proof -
  have "mle n f (bool_point n idx :: 'f list) =
        (\<Sum>idx' < 2 ^ n. (if idx = idx' then 1 else 0) * f idx')"
    unfolding mle_def
  proof (intro sum.cong refl)
    fix idx' :: nat assume "idx' \<in> {..< 2 ^ n}"
    then show "eq_pi (bool_point n idx :: 'f list) idx' * f idx' =
               (if idx = idx' then 1 else 0) * f idx'"
      by (simp add: eq_pi_bool_point assms)
  qed
  also have "\<dots> = (\<Sum>idx' < 2 ^ n. if idx = idx' then f idx' else 0)"
    by (intro sum.cong refl) simp
  also have "\<dots> = f idx"
    using assms by (simp add: sum.delta')
  finally show ?thesis .
qed

text \<open>Linearity in the table - the workhorse for wiring-MLE equalities
  (multiset repartition arguments, lemma (c)).\<close>

lemma mle_add:
  "mle n (\<lambda>i. f i + g i) pt = mle n f pt + mle n g pt"
  by (simp add: mle_def sum.distrib algebra_simps)

lemma mle_cong:
  assumes "\<And>i. i < 2 ^ n \<Longrightarrow> f i = g i"
  shows "mle n f pt = mle n g pt"
  unfolding mle_def by (intro sum.cong refl) (use assms in simp)

lemma mle_zero: "mle n (\<lambda>_. 0) pt = 0"
  by (simp add: mle_def)

lemma mle_scale:
  "mle n (\<lambda>i. c * f i) pt = c * mle n f pt"
  by (simp add: mle_def sum_distrib_left algebra_simps)

section \<open>The all-zero indicator (beta)\<close>

text \<open>\<open>beta pt = eq_pi pt 0\<close> = product of \<open>1 - pt!j\<close> (Rust: \<open>beta_eval\<close>).\<close>

definition beta :: "'f::comm_ring_1 list \<Rightarrow> 'f" where
  "beta pt = eq_pi pt 0"

lemma beta_prod: "beta pt = (\<Prod>j < length pt. 1 - pt ! j)"
proof -
  have "\<not> bit_at (length pt) 0 j" for j
    by (simp add: bit_at_def)
  then show ?thesis by (simp add: beta_def eq_pi_def)
qed

text \<open>Boolean instance: beta is 1 exactly at the all-zero point, and the
  weights over the hypercube sum to 1 (the unary-term lifting identity).\<close>

lemma beta_bool_point:
  assumes "idx < 2 ^ n"
  shows "beta (bool_point n idx :: 'f::comm_ring_1 list) = (if idx = 0 then 1 else 0)"
proof -
  have "(0 :: nat) < 2 ^ n" by simp
  then show ?thesis
    using eq_pi_bool_point[OF assms, of 0] by (simp add: beta_def)
qed

lemma sum_beta_bool_points:
  "(\<Sum>idx < (2 :: nat) ^ n. beta (bool_point n idx :: 'f::comm_ring_1 list)) = 1"
proof -
  have "(\<Sum>idx < (2 :: nat) ^ n. beta (bool_point n idx :: 'f list)) =
        (\<Sum>idx < (2 :: nat) ^ n. if idx = 0 then (1 :: 'f) else 0)"
    by (intro sum.cong refl) (simp add: beta_bool_point)
  also have "\<dots> = 1" by simp
  finally show ?thesis .
qed

end
