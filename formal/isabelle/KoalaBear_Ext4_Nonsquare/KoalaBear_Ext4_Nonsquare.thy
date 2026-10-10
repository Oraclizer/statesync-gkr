theory KoalaBear_Ext4_Nonsquare
  imports
    SMT_Circuit_Compiler_Correctness.Composition_Instance
    "HOL-Decision_Procs.Commutative_Ring"
    "HOL-Number_Theory.Quadratic_Reciprocity"
begin

section \<open>KoalaBear nonsquare certificates\<close>

text \<open>
  This stage owns only the number-theoretic facts required by the later
  quadratic tower. It deliberately contains no extension-field datatype,
  field instance, cardinality theorem, embedding, MLE lift, GKR theorem, or
  mutation claim.
\<close>

lemma three_is_not_a_quadratic_residue_mod_three:
  "\<not> QuadRes 3 2"
proof
  assume "QuadRes 3 2"
  then obtain y :: int where y: "[y ^ 2 = 2] (mod 3)"
    unfolding QuadRes_def by blast
  have lower: "0 \<le> y mod 3" by simp
  have upper: "y mod 3 < 3" by simp
  have cases: "y mod 3 = 0 \<or> y mod 3 = 1 \<or> y mod 3 = 2"
    using lower upper by presburger
  have "(y mod 3) ^ 2 mod 3 = 2"
    using y by (simp add: cong_def power_mod)
  with cases show False by auto
qed

lemma legendre_kb_p_mod_three:
  "Legendre 2130706433 3 = -1"
proof -
  have nqr: "\<not> QuadRes 3 (2130706433 :: int)"
    using three_is_not_a_quadratic_residue_mod_three
    by (simp add: QuadRes_def cong_def)
  show ?thesis
    using nqr by (simp add: Legendre_def cong_def)
qed

lemma legendre_three_mod_kb_p:
  "Legendre 3 2130706433 = -1"
proof -
  have qr_raw:
    "Legendre 3 2130706433 * Legendre 2130706433 3 =
       (-1 :: int) ^ nat ((((3 :: int) - 1) div 2) *
         (((2130706433 :: int) - 1) div 2))"
    apply (rule Quadratic_Reciprocity_int[of "3" "2130706433"])
    subgoal by simp
    subgoal by simp
    subgoal
      apply (subst nat_numeral)
      apply (rule kb_p_prime_nat)
      done
    subgoal by simp
    subgoal by simp
    done
  have even_exponent:
    "even (nat ((((3 :: int) - 1) div 2) *
      (((2130706433 :: int) - 1) div 2)))"
    by simp
  have sign:
    "(-1 :: int) ^ nat ((((3 :: int) - 1) div 2) *
      (((2130706433 :: int) - 1) div 2)) = 1"
    by (rule neg_one_even_power[OF even_exponent])
  have qr:
    "Legendre 3 2130706433 * Legendre 2130706433 3 = (1 :: int)"
    by (simp only: qr_raw sign)
  show ?thesis using qr legendre_kb_p_mod_three by simp
qed

lemma three_is_not_a_quadratic_residue_mod_kb_p:
  "\<not> QuadRes 2130706433 3"
proof
  assume qr: "QuadRes 2130706433 3"
  have nz: "\<not> [(3 :: int) = 0] (mod 2130706433)"
    by (simp add: cong_def)
  have "Legendre 3 2130706433 = 1"
    using qr nz by (simp add: Legendre_def)
  with legendre_three_mod_kb_p show False by simp
qed

lemma kb_val_three:
  "kb_val (3 :: koala_bear) = 3"
proof -
  have v: "kb_val (of_nat (3 :: nat) :: koala_bear) = int 3 mod kb_p"
    by (rule kb_val_of_nat)
  show ?thesis using v by (simp add: kb_p_def)
qed

lemma kb_three_nonsquare:
  "\<nexists>x :: koala_bear. x * x = 3"
proof
  assume "\<exists>x :: koala_bear. x * x = 3"
  then obtain x :: koala_bear where x2: "x * x = 3" by blast
  have "QuadRes 2130706433 3"
    unfolding QuadRes_def
  proof
    show "[(kb_val x) ^ 2 = (3 :: int)] (mod 2130706433)"
      using arg_cong[OF x2, of kb_val]
      by (simp add: cong_def power2_eq_square times_koala_bear.rep_eq
          kb_val_three kb_p_def)
  qed
  with three_is_not_a_quadratic_residue_mod_kb_p show False by contradiction
qed

lemma kb_sqrt_minus_one_mod_exp:
  "((2113994754 :: int) * 2113994754) mod kb_p = kb_p - 1"
  unfolding kb_p_def by eval

lemma kb_sqrt_minus_one:
  "(2113994754 :: koala_bear) * 2113994754 = -1"
proof -
  have i_val: "kb_val (2113994754 :: koala_bear) = 2113994754"
  proof -
    have v: "kb_val (of_nat (2113994754 :: nat) :: koala_bear) =
        int 2113994754 mod kb_p"
      by (rule kb_val_of_nat)
    show ?thesis using v by (simp add: kb_p_def)
  qed
  have lhs:
    "kb_val ((2113994754 :: koala_bear) * 2113994754) = kb_p - 1"
  proof -
    have "kb_val ((2113994754 :: koala_bear) * 2113994754) =
        (kb_val (2113994754 :: koala_bear) *
          kb_val (2113994754 :: koala_bear)) mod kb_p"
      by (simp only: times_koala_bear.rep_eq)
    also have "... = ((2113994754 :: int) * 2113994754) mod kb_p"
      by (simp only: i_val)
    also have "... = kb_p - 1"
      by (rule kb_sqrt_minus_one_mod_exp)
    finally show ?thesis .
  qed
  have rhs: "kb_val (-1 :: koala_bear) = kb_p - 1"
    by (simp add: uminus_koala_bear.rep_eq one_koala_bear.rep_eq kb_p_def)
  show ?thesis
    apply (rule iffD1[OF kb_val_inject])
    apply (rule trans[OF lhs])
    apply (rule sym[OF rhs])
    done
qed

lemma kb_minus_three_nonsquare:
  "\<nexists>x :: koala_bear. x * x = -3"
proof
  assume "\<exists>x :: koala_bear. x * x = -3"
  then obtain x :: koala_bear where x2: "x * x = -3" by blast
  let ?i = "2113994754 :: koala_bear"
  have "(?i * x) * (?i * x) = 3"
  proof -
    have "(?i * x) * (?i * x) = (?i * ?i) * (x * x)"
      by (simp only: mult.assoc mult.left_commute mult.commute)
    also have "... = (-1) * (-3)"
      by (simp only: kb_sqrt_minus_one x2)
    also have "... = 3" by simp
    finally show ?thesis .
  qed
  then have "\<exists>y :: koala_bear. y * y = 3" by blast
  with kb_three_nonsquare show False by contradiction
qed

end
