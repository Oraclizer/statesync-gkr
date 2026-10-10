(*
  Title:   KoalaBear_Field.thy
  Session: SMT_Circuit_Compiler_Correctness (SMT-specific layer)

  The KoalaBear prime field GF(2^31 - 2^24 + 1) as an Isabelle type.

  This is the concrete wire field of the frozen core (plonky3
  p3-koala-bear): the field the compiled circuits
  and the production prover operate over.  It exists in this development
  for ONE purpose - non-vacuity: the compiler_model /
  statesync_gkr_v01 locales are instantiated over an actual finite field
  with the production characteristic, so every theorem of this
  development is witnessed inhabited.

  The construction is the standard quotient {0..<p} with mod-p
  arithmetic.  Primality is established by sqrt-bounded trial division
  (evaluated by the code generator); the multiplicative inverse exists
  by the finite-integral-domain argument (multiplication by a nonzero
  element is injective, hence surjective, on a finite carrier) - no
  Bezout/Cong machinery is needed.
*)

theory KoalaBear_Field
  imports
    "HOL-Computational_Algebra.Primes"
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Cardinality"
begin
  \<comment> \<open>\<open>Code_Target_Numeral\<close> maps nat/int arithmetic to native ML integers for
     the primality sweep evaluation below; the plain HOL code equations
     compute \<open>mod\<close> by REPEATED SUBTRACTION, which makes the 46k-divisor
     sweep over a 31-bit prime computationally infeasible (observed).\<close>

section \<open>The KoalaBear prime\<close>

definition kb_p :: int where
  "kb_p = 2130706433"  \<comment> \<open>\<open>2^31 - 2^24 + 1\<close>\<close>

lemma kb_p_val: "kb_p = 2 ^ 31 - 2 ^ 24 + 1"
  by (simp add: kb_p_def)

lemma kb_p_pos: "0 < kb_p"
  by (simp add: kb_p_def)

lemma kb_p_gt1: "1 < kb_p"
  by (simp add: kb_p_def)

text \<open>
  Primality by sqrt-bounded trial division: any composite \<open>p = a * b\<close>
  with \<open>1 < a \<le> b\<close> has \<open>a * a \<le> p\<close>, so checking divisors up to
  \<open>\<lfloor>sqrt p\<rfloor> = 46159\<close> suffices.  The finite divisor sweep is discharged
  by evaluation.
\<close>

lemma nat_prime_sqrt_criterion:
  fixes p :: nat
  assumes gt: "1 < p"
    and nd: "\<And>n. 2 \<le> n \<Longrightarrow> n * n \<le> p \<Longrightarrow> \<not> n dvd p"
  shows "prime p"
proof (rule ccontr)
  assume "\<not> prime p"
  then obtain a where a_dvd: "a dvd p" and a_ne1: "a \<noteq> 1" and a_nep: "a \<noteq> p"
    using gt by (auto simp add: prime_nat_iff)
  from a_dvd obtain b where p_ab: "p = a * b" ..
  have a_pos: "0 < a"
  proof (rule ccontr)
    assume "\<not> 0 < a"
    then have "a = 0" by simp
    with p_ab gt show False by simp
  qed
  have b_pos: "0 < b"
  proof (rule ccontr)
    assume "\<not> 0 < b"
    then have "b = 0" by simp
    with p_ab gt show False by simp
  qed
  have a2: "2 \<le> a" using a_pos a_ne1 by simp
  have b_ne1: "b \<noteq> 1" using p_ab a_nep by auto
  have b2: "2 \<le> b" using b_pos b_ne1 by simp
  show False
  proof (cases "a \<le> b")
    case True
    then have "a * a \<le> p" using p_ab a_pos by (simp add: mult_le_mono2)
    with nd[OF a2 this] a_dvd show False by simp
  next
    case False
    then have "b * b \<le> p" using p_ab b_pos
      by (simp add: mult.commute mult_le_mono2)
    moreover have "b dvd p" using p_ab by auto
    ultimately show False using nd[OF b2] by simp
  qed
qed

lemma kb_p_prime_nat: "prime (2130706433 :: nat)"
proof (rule nat_prime_sqrt_criterion)
  show "1 < (2130706433 :: nat)" by simp
next
  fix n :: nat assume n2: "2 \<le> n" and nsq: "n * n \<le> 2130706433"
  have nb: "n \<le> 46159"
  proof (rule ccontr)
    assume "\<not> n \<le> 46159"
    then have "46160 \<le> n" by simp
    then have "(46160 :: nat) * 46160 \<le> n * n"
      by (intro mult_le_mono) simp_all
    with nsq show False by simp
  qed
  have sweep: "\<forall>m \<in> {2..46159 :: nat}. \<not> m dvd 2130706433" by eval
  have "n \<in> {2..46159 :: nat}" using n2 nb by simp
  then show "\<not> n dvd 2130706433"
    by (rule bspec[OF sweep])
      \<comment> \<open>explicit bspec: feeding the 46k-element ball fact to simp/auto
         invites an interval-expansion term blow-up\<close>
qed

lemma kb_p_prime: "prime kb_p"
    \<comment> \<open>via the nat-projection form, fully by resolution: handing a
       \<open>prime (numeral \<dots>)\<close> goal to simp invites a divergent search
       (observed), and the \<open>int n\<close>-pattern transfer rule never fires on
       a numeral goal (the embedding normalises away)\<close>
  unfolding kb_p_def prime_int_nat_transfer nat_numeral
  by (intro conjI kb_p_prime_nat) simp

section \<open>The field type\<close>

typedef koala_bear = "{0..<kb_p}"
  morphisms kb_val KB
  using kb_p_pos by (intro exI[of _ 0]) simp

setup_lifting type_definition_koala_bear

instantiation koala_bear :: comm_ring_1
begin

lift_definition zero_koala_bear :: koala_bear is 0
  using kb_p_pos by simp

lift_definition one_koala_bear :: koala_bear is 1
  using kb_p_gt1 by simp

lift_definition plus_koala_bear :: "koala_bear \<Rightarrow> koala_bear \<Rightarrow> koala_bear" is
  "\<lambda>x y. (x + y) mod kb_p"
  using kb_p_pos by simp

lift_definition uminus_koala_bear :: "koala_bear \<Rightarrow> koala_bear" is
  "\<lambda>x. (- x) mod kb_p"
  using kb_p_pos by simp

lift_definition minus_koala_bear :: "koala_bear \<Rightarrow> koala_bear \<Rightarrow> koala_bear" is
  "\<lambda>x y. (x - y) mod kb_p"
  using kb_p_pos by simp

lift_definition times_koala_bear :: "koala_bear \<Rightarrow> koala_bear \<Rightarrow> koala_bear" is
  "\<lambda>x y. (x * y) mod kb_p"
  using kb_p_pos by simp

instance
proof
    \<comment> \<open>every goal is discharged by a DETERMINISTIC minimal rewrite
       sequence: the blanket \<open>mod_simps + algebra_simps\<close> combination
       diverges on these goals (observed: multi-GB simp blow-up), the
       environment-sensitive-simp trap this corpus guards against\<close>
  fix a b c :: koala_bear
  show "a + b + c = a + (b + c)"
    by transfer (simp only: mod_add_left_eq mod_add_right_eq add.assoc)
  show "a + b = b + a"
    by transfer (simp only: add.commute)
  show "0 + a = a"
    by transfer (simp add: mod_pos_pos_trivial)
  show "- a + a = 0"
    by (transfer, simp only: mod_add_left_eq) simp
  show "a - b = a + - b"
    by (transfer, simp only: mod_add_right_eq) simp
  show "a * b * c = a * (b * c)"
    by transfer (simp only: mod_mult_left_eq mod_mult_right_eq mult.assoc)
  show "a * b = b * a"
    by transfer (simp only: mult.commute)
  show "1 * a = a"
    by transfer (simp add: mod_pos_pos_trivial)
  show "(a + b) * c = a * c + b * c"
    by transfer
       (simp only: mod_mult_left_eq mod_add_left_eq mod_add_right_eq
                   distrib_right)
  show "(0 :: koala_bear) \<noteq> 1"
    by transfer (simp add: kb_p_def)
qed

end

lemma UNIV_koala_bear: "(UNIV :: koala_bear set) = KB ` {0..<kb_p}"
proof
  show "(UNIV :: koala_bear set) \<subseteq> KB ` {0..<kb_p}"
  proof
    fix z :: koala_bear
    have "z = KB (kb_val z)" by (simp add: kb_val_inverse)
    moreover have "kb_val z \<in> {0..<kb_p}" by (rule kb_val)
    ultimately show "z \<in> KB ` {0..<kb_p}" by blast
  qed
qed simp

instance koala_bear :: finite
proof
  show "finite (UNIV :: koala_bear set)"
    unfolding UNIV_koala_bear by simp
qed

lemma CARD_koala_bear: "CARD(koala_bear) = 2130706433"
proof -
  have inj: "inj_on KB {0..<kb_p}"
  proof (rule inj_onI)
    fix a b assume a: "a \<in> {0..<kb_p}" and b: "b \<in> {0..<kb_p}"
      and eq: "KB a = KB b"
    have "kb_val (KB a) = kb_val (KB b)" using eq by simp
    with a b show "a = b" by (simp add: KB_inverse)
  qed
  have "CARD(koala_bear) = card (KB ` {0..<kb_p})"
    by (simp add: UNIV_koala_bear)
  also have "\<dots> = card {0..<kb_p}"
    by (rule card_image[OF inj])
  finally show ?thesis by (simp add: kb_p_def)
qed

section \<open>Field structure (finite integral domain argument)\<close>

lemma kb_not_dvd:
  assumes x: "x \<in> {0..<kb_p}" and ne: "x \<noteq> 0"
  shows "\<not> kb_p dvd x"
proof
  assume dvd: "kb_p dvd x"
  have "\<bar>kb_p\<bar> \<le> \<bar>x\<bar>"
    by (rule dvd_imp_le_int[OF ne dvd])
  with x kb_p_pos show False by auto
qed

lemma kb_mult_inj_on:
  assumes x: "x \<in> {0..<kb_p}" and ne: "x \<noteq> 0"
  shows "inj_on (\<lambda>y. (x * y) mod kb_p) {0..<kb_p}"
proof (rule inj_onI)
  fix y1 y2
  assume y1: "y1 \<in> {0..<kb_p}" and y2: "y2 \<in> {0..<kb_p}"
    and eq: "(x * y1) mod kb_p = (x * y2) mod kb_p"
  have "kb_p dvd (x * y1 - x * y2)"
    using eq by (simp add: mod_eq_dvd_iff)
  then have "kb_p dvd x * (y1 - y2)"
    by (simp add: algebra_simps)
  then have "kb_p dvd x \<or> kb_p dvd (y1 - y2)"
    using kb_p_prime by (simp add: prime_dvd_mult_iff)
  then have dvd_diff: "kb_p dvd (y1 - y2)"
    using kb_not_dvd[OF x ne] by blast
  have "y1 - y2 = 0"
  proof (rule ccontr)
    assume ne_diff: "y1 - y2 \<noteq> 0"
    have "\<bar>kb_p\<bar> \<le> \<bar>y1 - y2\<bar>"
      by (rule dvd_imp_le_int[OF ne_diff dvd_diff])
    moreover have "\<bar>y1 - y2\<bar> < kb_p" using y1 y2 by auto
    ultimately show False using kb_p_pos by simp
  qed
  then show "y1 = y2" by simp
qed

lemma kb_inverse_exists:
  assumes x: "x \<in> {0..<kb_p}" and ne: "x \<noteq> 0"
  shows "\<exists>y \<in> {0..<kb_p}. (x * y) mod kb_p = 1"
proof -
  have surj: "(\<lambda>y. (x * y) mod kb_p) ` {0..<kb_p} = {0..<kb_p}"
  proof (rule endo_inj_surj)
    show "finite {0..<kb_p}" by simp
    show "(\<lambda>y. (x * y) mod kb_p) ` {0..<kb_p} \<subseteq> {0..<kb_p}"
      using kb_p_pos by auto
    show "inj_on (\<lambda>y. (x * y) mod kb_p) {0..<kb_p}"
      by (rule kb_mult_inj_on[OF x ne])
  qed
  have "(1 :: int) \<in> (\<lambda>y. (x * y) mod kb_p) ` {0..<kb_p}"
    using surj kb_p_gt1 by simp
  then obtain y where y: "y \<in> {0..<kb_p}" and eq1: "1 = (x * y) mod kb_p"
    by (rule imageE)
      \<comment> \<open>the orientation is fixed by an explicit \<open>[symmetric]\<close>: \<open>intro sym\<close>
         REPEATS its rule, and \<open>sym\<close> is its own inverse, so it recurses until
         the ML stack dies ("Unable to increase stack") - and the resulting
         interrupt cascade then hides the real errors in neighbouring proofs\<close>
  from y eq1 [symmetric] show ?thesis by blast
qed

instantiation koala_bear :: inverse
    \<comment> \<open>the class PARAMETERS (\<open>inverse\<close>, \<open>divide\<close>) are introduced here and the
       field AXIOMS are discharged by a separate \<open>instance\<close> below: the \<open>/\<close>
       notation is an abbreviation of class \<open>inverse\<close>, so it only elaborates
       against a REGISTERED arity - inside an \<open>instantiation \<dots> :: field\<close> block
       it fails with \<open>No type arity koala_bear :: inverse\<close>\<close>
begin

text \<open>The inverse is a PLAIN definition through the representation
  (not a \<open>lift_definition\<close>: the lifting/code machinery diverges on the
  Hilbert-choice body - observed), with the field axioms proved at the
  representation level by injectivity of \<open>kb_val\<close>.\<close>

definition inverse_koala_bear :: "koala_bear \<Rightarrow> koala_bear" where
  "inverse_koala_bear a =
     KB (if kb_val a = 0 then 0
         else (SOME y. y \<in> {0..<kb_p} \<and> (kb_val a * y) mod kb_p = 1))"

definition divide_koala_bear :: "koala_bear \<Rightarrow> koala_bear \<Rightarrow> koala_bear" where
  "divide_koala_bear x y = x * inverse y"

instance ..

end

instance koala_bear :: field
proof
  fix a b :: koala_bear
  show "a \<noteq> 0 \<Longrightarrow> inverse a * a = 1"
  proof -
    assume ne: "a \<noteq> 0"
    have vne: "kb_val a \<noteq> 0"
    proof
      assume "kb_val a = 0"
      then have "kb_val a = kb_val (0 :: koala_bear)"
        by (simp add: zero_koala_bear.rep_eq)
      then have "a = 0" by (simp add: kb_val_inject)
      with ne show False ..
    qed
    define invv where
      "invv = (SOME y. y \<in> {0..<kb_p} \<and> (kb_val a * y) mod kb_p = 1)"
    from kb_inverse_exists[OF kb_val vne] obtain y
      where "y \<in> {0..<kb_p} \<and> (kb_val a * y) mod kb_p = 1" by blast
    then have someP: "invv \<in> {0..<kb_p} \<and> (kb_val a * invv) mod kb_p = 1"
      unfolding invv_def by (rule someI)
    have inv_a: "inverse a = KB invv"
      unfolding inverse_koala_bear_def invv_def
      by (rule arg_cong[of _ _ KB]) (rule if_not_P[OF vne])
    have rep_inv: "kb_val (inverse a) = invv"
      unfolding inv_a
      by (rule KB_inverse) (rule conjunct1[OF someP])
    have "kb_val (inverse a * a) = (invv * kb_val a) mod kb_p"
      by (simp add: times_koala_bear.rep_eq rep_inv)
    also have "\<dots> = (kb_val a * invv) mod kb_p"
      by (simp only: mult.commute)
    also have "\<dots> = 1"
      by (rule conjunct2[OF someP])
    also have "(1 :: int) = kb_val (1 :: koala_bear)"
      by (simp add: one_koala_bear.rep_eq)
    finally show "inverse a * a = 1"
      by (simp add: kb_val_inject)
  qed
  show "a / b = a * inverse b"
    by (simp add: divide_koala_bear_def)
  show "inverse (0 :: koala_bear) = 0"
  proof -
    have "inverse (0 :: koala_bear) = KB 0"
      unfolding inverse_koala_bear_def
      by (rule arg_cong[of _ _ KB]) (simp add: zero_koala_bear.rep_eq)
    also have "\<dots> = (0 :: koala_bear)"
    proof -
      have "kb_val (KB 0) = kb_val (0 :: koala_bear)"
        using kb_p_pos
        by (simp add: KB_inverse zero_koala_bear.rep_eq)
      then show ?thesis by (simp add: kb_val_inject)
    qed
    finally show ?thesis .
  qed
qed

section \<open>Concrete facts the instantiations consume\<close>

text \<open>The tag values 0/1/2 are pairwise distinct (odd characteristic).\<close>

lemma kb_two_val: "kb_val (2 :: koala_bear) = 2"
    \<comment> \<open>the rewrite must reach \<open>rep_eq\<close> BEFORE the numeral rules fold
       \<open>1 + 1\<close> back into \<open>2\<close>, hence the \<open>simp only\<close> stage and the
       \<open>unfolding\<close> (not \<open>simp only\<close>) transfer of the folded form\<close>
proof -
  have two: "(2 :: koala_bear) = 1 + 1" by simp
  have "kb_val ((1 :: koala_bear) + 1) = (1 + 1) mod kb_p"
    by (simp only: plus_koala_bear.rep_eq one_koala_bear.rep_eq)
  also have "\<dots> = 2"
    by (simp add: kb_p_def)
  finally show ?thesis unfolding two .
qed

lemma kb_two_ne_zero: "(2 :: koala_bear) \<noteq> 0"
proof
  assume "(2 :: koala_bear) = 0"
  then have "kb_val (2 :: koala_bear) = kb_val (0 :: koala_bear)" by simp
  then show False by (simp add: kb_two_val zero_koala_bear.rep_eq)
qed

lemma kb_two_ne_one: "(2 :: koala_bear) \<noteq> 1"
proof
  assume "(2 :: koala_bear) = 1"
  then have "kb_val (2 :: koala_bear) = kb_val (1 :: koala_bear)" by simp
  then show False by (simp add: kb_two_val one_koala_bear.rep_eq)
qed

text \<open>\<open>of_nat\<close> is the mod-p embedding: the ground fact for discharging
  the \<open>of_nat\<close>-injectivity-on-bound premises of lemma (b) in this
  concrete field.\<close>

lemma kb_val_of_nat: "kb_val (of_nat n) = int n mod kb_p"
proof (induction n)
  case 0 then show ?case using kb_p_pos by (simp add: zero_koala_bear.rep_eq)
next
  case (Suc n)
  have "kb_val (of_nat (Suc n)) = (1 + kb_val (of_nat n)) mod kb_p"
    by (simp add: plus_koala_bear.rep_eq one_koala_bear.rep_eq kb_p_gt1)
  also have "\<dots> = (1 + int n mod kb_p) mod kb_p" by (simp add: Suc.IH)
  also have "\<dots> = int (Suc n) mod kb_p"
    by (simp only: mod_add_right_eq) simp
  finally show ?case .
qed

lemma kb_of_nat_inj_on_bound:
  assumes m: "m < 2130706433" and n: "n < 2130706433"
    and eq: "(of_nat m :: koala_bear) = of_nat n"
  shows "m = n"
proof -
  have vm: "kb_val (of_nat m :: koala_bear) = kb_val (of_nat n :: koala_bear)"
    using eq by simp
  have im: "int m < kb_p" using m unfolding kb_p_def by simp
  have inn: "int n < kb_p" using n unfolding kb_p_def by simp
  have m_triv: "int m mod kb_p = int m"
    by (rule mod_pos_pos_trivial) (simp_all add: im)
  have n_triv: "int n mod kb_p = int n"
    by (rule mod_pos_pos_trivial) (simp_all add: inn)
  have "int m = int n"
    using vm unfolding kb_val_of_nat m_triv n_triv .
  then show ?thesis by simp
qed

end
