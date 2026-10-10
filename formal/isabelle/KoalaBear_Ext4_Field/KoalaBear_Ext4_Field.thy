theory KoalaBear_Ext4_Field
  imports KoalaBear_Ext4_Nonsquare.KoalaBear_Ext4_Nonsquare
begin

section \<open>Exact quadratic tower for KoalaBear[X]/(X^4 - 3)\<close>

text \<open>
  The pinned Rust type is the binomial extension with basis
  \<open>1, X, X^2, X^3\<close> and relation \<open>X^4 = 3\<close>. This stage owns
  the two quadratic extensions, their field and finiteness instances, exact
  cardinality, and the base-field embedding. It owns no MLE, circuit, GKR,
  uniformity, or mutation result.
\<close>

instance koala_bear :: finite_field
  by (rule finite_fieldI) simp

datatype kb_quad = KBQ koala_bear koala_bear

fun q0 :: "kb_quad \<Rightarrow> koala_bear" where "q0 (KBQ a b) = a"
fun q1 :: "kb_quad \<Rightarrow> koala_bear" where "q1 (KBQ a b) = b"

instantiation kb_quad :: comm_ring_1
begin

definition zero_kb_quad where "zero_kb_quad = KBQ 0 0"
definition one_kb_quad where "one_kb_quad = KBQ 1 0"
fun plus_kb_quad where
  "KBQ a b + KBQ c d = KBQ (a + c) (b + d)"
fun uminus_kb_quad where
  "- KBQ a b = KBQ (-a) (-b)"
fun minus_kb_quad where
  "KBQ a b - KBQ c d = KBQ (a - c) (b - d)"
fun times_kb_quad where
  "KBQ a b * KBQ c d = KBQ (a*c + 3*b*d) (a*d + b*c)"

instance
proof
  fix a b c :: kb_quad
  show "a + b + c = a + (b + c)" by (cases a; cases b; cases c; simp)
  show "a + b = b + a" by (cases a; cases b; simp add: add.commute)
  show "0 + a = a" by (cases a; simp add: zero_kb_quad_def)
  show "-a + a = 0" by (cases a; simp add: zero_kb_quad_def)
  show "a - b = a + -b" by (cases a; cases b; simp)
  show "a * b * c = a * (b * c)"
    by (cases a; cases b; cases c; simp add: algebra_simps)
  show "a * b = b * a" by (cases a; cases b; simp add: algebra_simps)
  show "1 * a = a" by (cases a; simp add: one_kb_quad_def)
  show "(a + b) * c = a * c + b * c"
    by (cases a; cases b; cases c; simp add: algebra_simps)
  show "(0 :: kb_quad) \<noteq> 1" by (simp add: zero_kb_quad_def one_kb_quad_def)
qed

end

lemma KBQ_zero: "KBQ 0 0 = (0 :: kb_quad)"
  by (simp add: zero_kb_quad_def)

lemma KBQ_one: "KBQ 1 0 = (1 :: kb_quad)"
  by (simp add: one_kb_quad_def)

lemma of_nat_kb_quad:
  "(of_nat n :: kb_quad) = KBQ (of_nat n) 0"
  by (induction n) (simp_all add: zero_kb_quad_def one_kb_quad_def)

lemma KBQ_three: "KBQ 3 0 = (3 :: kb_quad)"
proof -
  have "(3 :: kb_quad) = 1 + 1 + 1" by simp
  also have "... = KBQ 3 0" by (simp add: one_kb_quad_def)
  finally show ?thesis by simp
qed

lemma kb_quad_norm_zero_iff:
  "a * a - 3 * b * b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  for a b :: koala_bear
proof
  assume h: "a * a - 3 * b * b = 0"
  show "a = 0 \<and> b = 0"
  proof (cases "b = 0")
    case True
    with h show ?thesis by simp
  next
    case False
    from h have "(a / b) * (a / b) = 3"
      using False by (simp add: field_simps; ring)
    then have "\<exists>x :: koala_bear. x * x = 3" by blast
    with kb_three_nonsquare show ?thesis by contradiction
  qed
qed simp

lemma kb_quad_inverse_exists:
  assumes "z \<noteq> 0"
  shows "\<exists>w :: kb_quad. z * w = 1"
proof (cases z)
  case (KBQ a b)
  let ?n = "a * a - 3 * b * b"
  have n0: "?n \<noteq> 0"
  proof
    assume nzero: "?n = 0"
    have ab0: "a = 0 \<and> b = 0"
      using kb_quad_norm_zero_iff[of a b] nzero by simp
    from ab0 have a0: "a = 0" and b0: "b = 0" by auto
    have z00: "z = KBQ 0 0" unfolding KBQ using a0 b0 by simp
    have "z = 0" using z00 KBQ_zero by simp
    with assms show False by contradiction
  qed
  let ?w = "KBQ (a / ?n) (-b / ?n)"
  have c0: "a * (a / ?n) + 3 * b * (-b / ?n) = 1"
  proof -
    have "a * (a / ?n) + 3 * b * (-b / ?n) = ?n * inverse ?n"
      by (simp add: divide_inverse algebra_simps)
    also have "... = 1" using n0 by simp
    finally show ?thesis .
  qed
  have c1: "a * (-b / ?n) + b * (a / ?n) = 0"
    by (simp add: divide_inverse algebra_simps)
  have "z * ?w = 1"
    unfolding KBQ using c0 c1
    by (simp add: one_kb_quad_def)
  then show ?thesis by blast
qed

instantiation kb_quad :: inverse
begin

definition inverse_kb_quad :: "kb_quad \<Rightarrow> kb_quad" where
  "inverse_kb_quad z = (if z = 0 then 0 else (SOME w. z * w = 1))"
definition divide_kb_quad :: "kb_quad \<Rightarrow> kb_quad \<Rightarrow> kb_quad" where
  "divide_kb_quad x y = x * inverse y"
instance ..

end

instance kb_quad :: field
proof
  fix a b :: kb_quad
  show "a \<noteq> 0 \<Longrightarrow> inverse a * a = 1"
  proof -
    assume a0: "a \<noteq> 0"
    have "a * inverse a = 1"
      unfolding inverse_kb_quad_def
      using someI_ex[OF kb_quad_inverse_exists[OF a0]] a0 by simp
    then show "inverse a * a = 1" by (simp add: mult.commute)
  qed
  show "a / b = a * inverse b" by (simp add: divide_kb_quad_def)
  show "inverse (0 :: kb_quad) = 0" by (simp add: inverse_kb_quad_def)
qed

instance kb_quad :: finite
proof
  have cover:
    "(UNIV :: kb_quad set) \<subseteq>
      (\<lambda>(a,b). KBQ a b) ` (UNIV :: (koala_bear \<times> koala_bear) set)"
  proof
    fix z :: kb_quad
    assume "z \<in> UNIV"
    obtain a b where z: "z = KBQ a b" by (cases z) auto
    have ctor_mem: "KBQ a b \<in> range (\<lambda>(a,b). KBQ a b)"
      by (rule range_eqI[where x="(a,b)"]) simp
    show "z \<in> (\<lambda>(a,b). KBQ a b) ` UNIV"
      using z ctor_mem by simp
  qed
  have fin_image: "finite ((\<lambda>(a,b). KBQ a b) `
      (UNIV :: (koala_bear \<times> koala_bear) set))" by simp
  show "finite (UNIV :: kb_quad set)"
    by (rule finite_subset[OF cover fin_image])
qed

definition kb_y :: kb_quad where "kb_y = KBQ 0 1"

lemma kb_y_square [simp]: "kb_y * kb_y = 3"
  by (simp add: kb_y_def KBQ_three)

lemma kb_quad_y_nonsquare:
  "\<nexists>z :: kb_quad. z * z = kb_y"
proof
  assume "\<exists>z :: kb_quad. z * z = kb_y"
  then obtain z where z2: "z * z = kb_y" by blast
  then obtain a b where z: "z = KBQ a b" by (cases z) auto
  from z2[unfolded z] have z2': "KBQ a b * KBQ a b = kb_y" .
  then have e0: "a*a + 3*b*b = 0" and e1_raw: "a*b + b*a = 1"
    by (simp_all add: kb_y_def)
  have e1: "2*a*b = 1"
  proof -
    have "2*a*b = a*b + b*a"
      by (simp add: numeral_eq_Suc algebra_simps)
    also have "... = 1" by (rule e1_raw)
    finally show ?thesis .
  qed
  have b0: "b \<noteq> 0" using e1 by auto
  have aa0: "a * a = -(3 * b * b)"
    using e0 by (simp only: eq_neg_iff_add_eq_0)
  have aa: "a * a = -3 * (b * b)"
    using aa0 by (simp add: algebra_simps)
  have bb0: "b * b \<noteq> 0" using b0 by simp
  have "(a / b) * (a / b) = -3"
  proof -
    have "(a / b) * (a / b) = (a * a) / (b * b)"
      by (simp add: divide_inverse; ring)
    also have "... = (-3 * (b * b)) / (b * b)" by (simp only: aa)
    also have "... = -3" using bb0 by simp
    finally show ?thesis .
  qed
  then have "\<exists>x :: koala_bear. x * x = -3" by blast
  with kb_minus_three_nonsquare show False by contradiction
qed

datatype koala_bear_ext4 = KBE kb_quad kb_quad

fun e0 :: "koala_bear_ext4 \<Rightarrow> kb_quad" where "e0 (KBE a b) = a"
fun e1 :: "koala_bear_ext4 \<Rightarrow> kb_quad" where "e1 (KBE a b) = b"

instantiation koala_bear_ext4 :: comm_ring_1
begin

definition zero_koala_bear_ext4 where "zero_koala_bear_ext4 = KBE 0 0"
definition one_koala_bear_ext4 where "one_koala_bear_ext4 = KBE 1 0"
fun plus_koala_bear_ext4 where
  "KBE a b + KBE c d = KBE (a + c) (b + d)"
fun uminus_koala_bear_ext4 where
  "- KBE a b = KBE (-a) (-b)"
fun minus_koala_bear_ext4 where
  "KBE a b - KBE c d = KBE (a - c) (b - d)"
fun times_koala_bear_ext4 where
  "KBE a b * KBE c d = KBE (a*c + kb_y*b*d) (a*d + b*c)"

instance
proof
  fix a b c :: koala_bear_ext4
  show "a + b + c = a + (b + c)" by (cases a; cases b; cases c; simp)
  show "a + b = b + a" by (cases a; cases b; simp add: add.commute)
  show "0 + a = a" by (cases a; simp add: zero_koala_bear_ext4_def)
  show "-a + a = 0" by (cases a; simp add: zero_koala_bear_ext4_def)
  show "a - b = a + -b" by (cases a; cases b; simp)
  show "a * b * c = a * (b * c)"
    by (cases a; cases b; cases c; simp add: algebra_simps)
  show "a * b = b * a" by (cases a; cases b; simp add: algebra_simps)
  show "1 * a = a"
    by (cases a; simp add: one_koala_bear_ext4_def KBQ_one KBQ_zero)
  show "(a + b) * c = a * c + b * c"
    by (cases a; cases b; cases c; simp add: algebra_simps)
  show "(0 :: koala_bear_ext4) \<noteq> 1"
    by (simp add: zero_koala_bear_ext4_def one_koala_bear_ext4_def KBQ_zero KBQ_one)
qed

end

lemma KBE_zero: "KBE 0 0 = (0 :: koala_bear_ext4)"
  by (simp add: zero_koala_bear_ext4_def)

lemma KBE_one: "KBE 1 0 = (1 :: koala_bear_ext4)"
  by (simp add: one_koala_bear_ext4_def)

lemma kb_ext4_norm_zero_iff:
  "a * a - kb_y * b * b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  for a b :: kb_quad
proof
  assume h: "a * a - kb_y * b * b = 0"
  show "a = 0 \<and> b = 0"
  proof (cases "b = 0")
    case True
    with h show ?thesis by simp
  next
    case False
    from h have "(a / b) * (a / b) = kb_y"
      using False by (simp add: field_simps; ring)
    then have "\<exists>x :: kb_quad. x * x = kb_y" by blast
    with kb_quad_y_nonsquare show ?thesis by contradiction
  qed
qed simp

lemma kb_ext4_inverse_exists:
  assumes "z \<noteq> 0"
  shows "\<exists>w :: koala_bear_ext4. z * w = 1"
proof (cases z)
  case (KBE a b)
  let ?n = "a * a - kb_y * b * b"
  have n0: "?n \<noteq> 0"
  proof
    assume nzero: "?n = 0"
    have ab0: "a = 0 \<and> b = 0"
      using kb_ext4_norm_zero_iff[of a b] nzero by simp
    from ab0 have a0: "a = 0" and b0: "b = 0" by auto
    have z00: "z = KBE 0 0" unfolding KBE using a0 b0 by simp
    have "z = 0" using z00 KBE_zero by simp
    with assms show False by contradiction
  qed
  let ?w = "KBE (a / ?n) (-b / ?n)"
  have c0: "a * (a / ?n) + kb_y * b * (-b / ?n) = 1"
  proof -
    have "a * (a / ?n) + kb_y * b * (-b / ?n) = ?n * inverse ?n"
      by (simp add: divide_inverse algebra_simps)
    also have "... = 1" using n0 by simp
    finally show ?thesis .
  qed
  have c1: "a * (-b / ?n) + b * (a / ?n) = 0"
    by (simp add: divide_inverse algebra_simps)
  have "z * ?w = 1"
    unfolding KBE using c0 c1
    by (simp add: one_koala_bear_ext4_def)
  then show ?thesis by blast
qed

instantiation koala_bear_ext4 :: inverse
begin

definition inverse_koala_bear_ext4 :: "koala_bear_ext4 \<Rightarrow> koala_bear_ext4" where
  "inverse_koala_bear_ext4 z = (if z = 0 then 0 else (SOME w. z * w = 1))"
definition divide_koala_bear_ext4 :: "koala_bear_ext4 \<Rightarrow> koala_bear_ext4 \<Rightarrow> koala_bear_ext4" where
  "divide_koala_bear_ext4 x y = x * inverse y"
instance ..

end

instance koala_bear_ext4 :: field
proof
  fix a b :: koala_bear_ext4
  show "a \<noteq> 0 \<Longrightarrow> inverse a * a = 1"
  proof -
    assume a0: "a \<noteq> 0"
    have "a * inverse a = 1"
      unfolding inverse_koala_bear_ext4_def
      using someI_ex[OF kb_ext4_inverse_exists[OF a0]] a0 by simp
    then show "inverse a * a = 1" by (simp add: mult.commute)
  qed
  show "a / b = a * inverse b" by (simp add: divide_koala_bear_ext4_def)
  show "inverse (0 :: koala_bear_ext4) = 0" by (simp add: inverse_koala_bear_ext4_def)
qed

instance koala_bear_ext4 :: finite
proof
  have cover:
    "(UNIV :: koala_bear_ext4 set) \<subseteq>
      (\<lambda>(a,b). KBE a b) ` (UNIV :: (kb_quad \<times> kb_quad) set)"
  proof
    fix z :: koala_bear_ext4
    assume "z \<in> UNIV"
    obtain a b where z: "z = KBE a b" by (cases z) auto
    have ctor_mem: "KBE a b \<in> range (\<lambda>(a,b). KBE a b)"
      by (rule range_eqI[where x="(a,b)"]) simp
    show "z \<in> (\<lambda>(a,b). KBE a b) ` UNIV"
      using z ctor_mem by simp
  qed
  have fin_image: "finite ((\<lambda>(a,b). KBE a b) `
      (UNIV :: (kb_quad \<times> kb_quad) set))" by simp
  show "finite (UNIV :: koala_bear_ext4 set)"
    by (rule finite_subset[OF cover fin_image])
qed

definition kb4_embed :: "koala_bear \<Rightarrow> koala_bear_ext4" where
  "kb4_embed x = KBE (KBQ x 0) 0"

definition kb_alpha :: koala_bear_ext4 where
  "kb_alpha = KBE 0 1"

lemma kb_alpha_square: "kb_alpha * kb_alpha = KBE kb_y 0"
  by (simp add: kb_alpha_def)

lemma kb_alpha_fourth: "kb_alpha ^ 4 = kb4_embed 3"
  by (simp add: power4_eq_xxxx kb_alpha_def kb_y_def kb4_embed_def)

lemma kb4_embed_simps [simp]:
  "kb4_embed 0 = 0"
  "kb4_embed 1 = 1"
  "kb4_embed (x + y) = kb4_embed x + kb4_embed y"
  "kb4_embed (x - y) = kb4_embed x - kb4_embed y"
  "kb4_embed (-x) = -kb4_embed x"
  "kb4_embed (x * y) = kb4_embed x * kb4_embed y"
  by (simp_all add: kb4_embed_def KBE_zero KBE_one KBQ_zero KBQ_one)

lemma kb4_embed_inj: "inj kb4_embed"
  by (rule injI) (simp add: kb4_embed_def)

lemma kb4_embed_eq_zero [simp]: "kb4_embed x = 0 \<longleftrightarrow> x = 0"
  using kb4_embed_inj by (metis inj_eq kb4_embed_simps(1))

lemma kb4_embed_inverse [simp]: "kb4_embed (inverse x) = inverse (kb4_embed x)"
proof (cases "x = 0")
  case False
  have "kb4_embed (inverse x) * kb4_embed x = kb4_embed (inverse x * x)"
    by (rule sym[OF kb4_embed_simps(6)])
  also have "... = kb4_embed 1" using False by simp
  also have "... = 1" by (rule kb4_embed_simps(2))
  finally have "kb4_embed (inverse x) * kb4_embed x = 1" .
  then have product: "kb4_embed x * kb4_embed (inverse x) = 1"
    by (simp add: mult.commute)
  have "inverse (kb4_embed x) = kb4_embed (inverse x)"
    by (rule inverse_unique[OF product])
  then show ?thesis by (rule sym)
qed simp

lemma kb_quad_ctor_bij: "bij (\<lambda>(a,b). KBQ a b)"
proof (rule bijI)
  show "inj (\<lambda>(a,b). KBQ a b)"
    apply (rule injI)
    subgoal for x y by (cases x; cases y; simp)
    done
  show "surj (\<lambda>(a,b). KBQ a b)"
    apply (rule surjI[where f="\<lambda>z. (q0 z, q1 z)"])
    subgoal for z by (cases z) simp
    done
qed

lemma kb_ext4_ctor_bij: "bij (\<lambda>(a,b). KBE a b)"
proof (rule bijI)
  show "inj (\<lambda>(a,b). KBE a b)"
    apply (rule injI)
    subgoal for x y by (cases x; cases y; simp)
    done
  show "surj (\<lambda>(a,b). KBE a b)"
    apply (rule surjI[where f="\<lambda>z. (e0 z, e1 z)"])
    subgoal for z by (cases z) simp
    done
qed

lemma CARD_kb_quad: "CARD(kb_quad) = 2130706433 ^ 2"
proof -
  have bij: "bij_betw (\<lambda>(a,b). KBQ a b)
      (UNIV :: (koala_bear \<times> koala_bear) set) (UNIV :: kb_quad set)"
    using kb_quad_ctor_bij by (simp add: bij_betw_def bij_def)
  have "CARD(kb_quad) = CARD(koala_bear \<times> koala_bear)"
    using bij_betw_same_card[OF bij] by simp
  also have "... = CARD(koala_bear) * CARD(koala_bear)" by simp
  also have "... = 2130706433 * 2130706433"
    by (simp only: CARD_koala_bear)
  also have "... = 2130706433 ^ 2" by (simp only: power2_eq_square)
  finally show ?thesis .
qed

lemma CARD_koala_bear_ext4:
  "CARD(koala_bear_ext4) = 2130706433 ^ 4"
proof -
  have bij: "bij_betw (\<lambda>(a,b). KBE a b)
      (UNIV :: (kb_quad \<times> kb_quad) set) (UNIV :: koala_bear_ext4 set)"
    using kb_ext4_ctor_bij by (simp add: bij_betw_def bij_def)
  have "CARD(koala_bear_ext4) = CARD(kb_quad \<times> kb_quad)"
    using bij_betw_same_card[OF bij] by simp
  also have "... = CARD(kb_quad) * CARD(kb_quad)" by simp
  also have "... = (2130706433 ^ 2) * (2130706433 ^ 2)"
    by (simp only: CARD_kb_quad)
  also have "... = 2130706433 ^ 4"
    by (simp add: power2_eq_square power4_eq_xxxx algebra_simps)
  finally show ?thesis .
qed

lemma kb_alpha_not_in_base: "kb_alpha \<notin> range kb4_embed"
  by (auto simp: kb_alpha_def kb4_embed_def)

text \<open>
  The two nonsquare certificates imported from the nonsquare session establish
  the irreducibility of the exact tower: \<open>Y^2 - 3\<close> over KoalaBear and
  \<open>X^2 - Y\<close> over the intermediate field.
\<close>

lemma kb_ext4_basis_unique:
  "KBE (KBQ a0 a2) (KBQ a1 a3) = 0 \<longleftrightarrow>
     a0 = 0 \<and> a1 = 0 \<and> a2 = 0 \<and> a3 = 0"
proof
  assume h: "KBE (KBQ a0 a2) (KBQ a1 a3) = 0"
  have h0: "KBQ a0 a2 = 0" and h1: "KBQ a1 a3 = 0"
    using h by (simp_all add: zero_koala_bear_ext4_def)
  have a0: "a0 = 0" and a2: "a2 = 0"
    using h0 by (simp_all add: zero_kb_quad_def)
  have a1: "a1 = 0" and a3: "a3 = 0"
    using h1 by (simp_all add: zero_kb_quad_def)
  show "a0 = 0 \<and> a1 = 0 \<and> a2 = 0 \<and> a3 = 0"
    using a0 a1 a2 a3 by blast
next
  assume "a0 = 0 \<and> a1 = 0 \<and> a2 = 0 \<and> a3 = 0"
  then show "KBE (KBQ a0 a2) (KBQ a1 a3) = 0"
    by (simp add: zero_koala_bear_ext4_def zero_kb_quad_def)
qed

end
