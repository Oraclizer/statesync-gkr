theory KoalaBear_Ext4_Lift
  imports KoalaBear_Ext4_Field.KoalaBear_Ext4_Field
begin

section \<open>Polynomial and multilinear-extension lifting\<close>

text \<open>
  This stage owns preservation from base-field tables and circuits into the
  exact quartic field. It imports only the quartic field session and owns no GKR soundness activation,
  challenge-distribution theorem, or mutation campaign.
\<close>

lemma kb4_embed_sum_list:
  "kb4_embed (sum_list xs) = sum_list (map kb4_embed xs)"
  by (induction xs) simp_all

lemma kb4_embed_prod_list:
  "kb4_embed (prod_list xs) = prod_list (map kb4_embed xs)"
  by (induction xs) simp_all

lemma kb4_embed_sum_lessThan:
  fixes f :: "nat \<Rightarrow> koala_bear"
  shows "kb4_embed (\<Sum>i<n. f i) = (\<Sum>i<n. kb4_embed (f i))"
  by (induction n) simp_all

lemma kb4_embed_prod_lessThan:
  fixes f :: "nat \<Rightarrow> koala_bear"
  shows "kb4_embed (\<Prod>i<n. f i) = (\<Prod>i<n. kb4_embed (f i))"
  by (induction n) simp_all

lemma kb4_embed_power [simp]: "kb4_embed (x ^ n) = kb4_embed x ^ n"
  by (induction n) simp_all

lemma kb4_embed_eq_pi:
  "eq_pi (map kb4_embed pt) idx = kb4_embed (eq_pi pt idx)"
  unfolding eq_pi_def
  apply (subst kb4_embed_prod_lessThan)
  apply (rule prod.cong)
  apply simp
  subgoal for j by (cases "bit_at (length pt) idx j") simp_all
  done

lemma kb4_embed_mle_base_point:
  "mle n (kb4_embed \<circ> f) (map kb4_embed pt) = kb4_embed (mle n f pt)"
  unfolding mle_def comp_def
  by (simp add: kb4_embed_sum_lessThan kb4_embed_eq_pi)

text \<open>
  The live Rust function \<open>mle_eval_base\<close> embeds every table value first
  and then folds at an arbitrary extension point. The corresponding semantic
  object is the extension-field MLE of the embedded table. It is not an
  embedded base-field evaluation unless the point lies in the base image.
\<close>

definition lifted_mle ::
  "nat \<Rightarrow> (nat \<Rightarrow> koala_bear) \<Rightarrow> koala_bear_ext4 list \<Rightarrow> koala_bear_ext4" where
  "lifted_mle n f pt = mle n (kb4_embed \<circ> f) pt"

lemma lifted_mle_boolean:
  assumes "idx < 2 ^ n"
  shows "lifted_mle n f (bool_point n idx) = kb4_embed (f idx)"
  using mle_bool_point[OF assms, where 'f=koala_bear_ext4]
  by (simp add: lifted_mle_def)

lemma lifted_mle_positive_witness:
  "lifted_mle 1 (\<lambda>i. if i = 0 then 1 else 2) [kb_alpha] = 1 + kb_alpha"
proof -
  have eq0: "eq_pi [kb_alpha] 0 = 1 - kb_alpha"
    by (simp add: eq_pi_def bit_at_def)
  have bit1: "bit_at (length [kb_alpha]) 1 0"
    by (simp add: bit_at_def bit_iff_odd)
  have eq1: "eq_pi [kb_alpha] 1 = kb_alpha"
  proof -
    have bit1': "bit_at (Suc 0) 1 0"
      using bit1 by simp
    let ?f = "\<lambda>j.
      if bit_at (Suc 0) 1 j then [kb_alpha] ! j
      else 1 - [kb_alpha] ! j"
    have expanded:
      "(\<Prod>j<length [kb_alpha].
          if bit_at (length [kb_alpha]) 1 j then [kb_alpha] ! j
          else 1 - [kb_alpha] ! j) = kb_alpha"
    proof -
      have "(\<Prod>j<length [kb_alpha].
          if bit_at (length [kb_alpha]) 1 j then [kb_alpha] ! j
          else 1 - [kb_alpha] ! j) = (\<Prod>j<Suc 0. ?f j)"
        by simp
      also have "... = ?f 0 * (\<Prod>j<0. ?f (Suc j))"
        by (rule prod_lessThan_Suc_shift)
      also have "... = kb_alpha"
        using bit1' by simp
      finally show ?thesis .
    qed
    show ?thesis
      unfolding eq_pi_def
      by (rule expanded)
  qed
  have alpha_arithmetic:
    "(1 - kb_alpha) * kb4_embed 1 + kb_alpha * kb4_embed 2 =
     1 + kb_alpha"
    by (simp add: kb_alpha_def kb4_embed_def zero_koala_bear_ext4_def
        one_koala_bear_ext4_def zero_kb_quad_def one_kb_quad_def algebra_simps)
  let ?t = "\<lambda>idx.
    eq_pi [kb_alpha] idx * kb4_embed (if idx = 0 then 1 else 2)"
  have sum_two:
    "(\<Sum>idx<Suc (Suc 0). ?t idx) = ?t 0 + ?t (Suc 0)"
  proof -
    have "(\<Sum>idx<Suc (Suc 0). ?t idx) =
      ?t 0 + (\<Sum>idx<Suc 0. ?t (Suc idx))"
      by (rule sum_lessThan_Suc_shift)
    also have "... =
      ?t 0 + (?t (Suc 0) + (\<Sum>idx<0. ?t (Suc (Suc idx))))"
      by (subst sum_lessThan_Suc_shift) (rule refl)
    also have "... = ?t 0 + ?t (Suc 0)" by simp
    finally show ?thesis .
  qed
  have upper: "(2 :: nat) ^ 1 = Suc (Suc 0)"
    by simp
  have sum_normal:
    "(\<Sum>idx<2 ^ 1. ?t idx) = ?t 0 + ?t (Suc 0)"
  proof -
    have "(\<Sum>idx<2 ^ 1. ?t idx) =
      (\<Sum>idx<Suc (Suc 0). ?t idx)"
      by (simp only: upper)
    also have "... = ?t 0 + ?t (Suc 0)"
      by (rule sum_two)
    finally show ?thesis .
  qed
  have term0:
    "?t 0 = eq_pi [kb_alpha] 0 * kb4_embed 1"
    by simp
  have term1:
    "?t (Suc 0) = eq_pi [kb_alpha] 1 * kb4_embed 2"
    by simp
  have sum_eval:
    "(\<Sum>idx<2 ^ 1. ?t idx) =
      eq_pi [kb_alpha] 0 * kb4_embed 1 +
      eq_pi [kb_alpha] 1 * kb4_embed 2"
    apply (rule trans[OF sum_normal])
    apply (simp only: term0 term1)
    done
  have first:
    "lifted_mle 1 (\<lambda>i. if i = 0 then 1 else 2) [kb_alpha] =
      eq_pi [kb_alpha] 0 * kb4_embed 1 +
      eq_pi [kb_alpha] 1 * kb4_embed 2"
    unfolding lifted_mle_def mle_def comp_def
    by (rule sum_eval)
  also have "... =
      (1 - kb_alpha) * kb4_embed 1 + kb_alpha * kb4_embed 2"
    using eq0 eq1 by simp
  also have "... = 1 + kb_alpha"
    by (rule alpha_arithmetic)
  finally show ?thesis .
qed

section \<open>Layer, circuit, and well-formedness lifting\<close>

definition lift_gate :: "koala_bear gate \<Rightarrow> koala_bear_ext4 gate" where
  "lift_gate g =
    \<lparr>g_kind = g_kind g,
      g_out = g_out g,
      g_in1 = g_in1 g,
      g_in2 = g_in2 g,
      g_coeff = kb4_embed (g_coeff g)\<rparr>"

definition lift_layer :: "koala_bear layer \<Rightarrow> koala_bear_ext4 layer" where
  "lift_layer L =
    \<lparr>layer_width_bits = layer_width_bits L,
      layer_gates = map lift_gate (layer_gates L),
      layer_consts = map (\<lambda>(i,c). (i, kb4_embed c)) (layer_consts L)\<rparr>"

definition lift_circuit :: "koala_bear layered_circuit \<Rightarrow> koala_bear_ext4 layered_circuit" where
  "lift_circuit C =
    \<lparr>circ_layers = map lift_layer (circ_layers C),
      input_width_bits = input_width_bits C\<rparr>"

lemma lift_gate_fields [simp]:
  "g_kind (lift_gate g) = g_kind g"
  "g_out (lift_gate g) = g_out g"
  "g_in1 (lift_gate g) = g_in1 g"
  "g_in2 (lift_gate g) = g_in2 g"
  "g_coeff (lift_gate g) = kb4_embed (g_coeff g)"
  by (simp_all add: lift_gate_def)

lemma gate_sem_embed:
  "gate_sem k (kb4_embed x) (kb4_embed y) = kb4_embed (gate_sem k x y)"
  by (cases k) (simp_all add: gate_sem_def)

lemma gate_contrib_embed:
  assumes "g_in1 g < length below" "g_in2 g < length below"
  shows "gate_contrib (lift_gate g) (map kb4_embed below) =
         kb4_embed (gate_contrib g below)"
  using assms by (simp add: gate_contrib_def gate_sem_embed)

lemma gate_contrib_sum_lift:
  assumes bounds:
    "\<And>g. g \<in> set gs \<Longrightarrow>
      g_in1 g < length below \<and> g_in2 g < length below"
  shows
    "sum_list
       (map (\<lambda>g. gate_contrib g (map kb4_embed below))
         (filter (\<lambda>g. g_out g = z) (map lift_gate gs))) =
     kb4_embed
       (sum_list
         (map (\<lambda>g. gate_contrib g below)
           (filter (\<lambda>g. g_out g = z) gs)))"
  using bounds
proof (induction gs)
  case Nil
  show ?case by simp
next
  case (Cons g gs)
  have g1: "g_in1 g < length below"
    using Cons.prems by simp
  have g2: "g_in2 g < length below"
    using Cons.prems by simp
  have tail:
    "h \<in> set gs \<Longrightarrow>
      g_in1 h < length below \<and> g_in2 h < length below" for h
    using Cons.prems by simp
  have ih:
    "sum_list
       (map (\<lambda>h. gate_contrib h (map kb4_embed below))
         (filter (\<lambda>h. g_out h = z) (map lift_gate gs))) =
     kb4_embed
       (sum_list
         (map (\<lambda>h. gate_contrib h below)
           (filter (\<lambda>h. g_out h = z) gs)))"
    by (rule Cons.IH[OF tail])
  have head:
    "gate_contrib (lift_gate g) (map kb4_embed below) =
     kb4_embed (gate_contrib g below)"
    by (rule gate_contrib_embed[OF g1 g2])
  show ?case
  proof (cases "g_out g = z")
    case True
    then show ?thesis using head ih by simp
  next
    case False
    then show ?thesis using ih by simp
  qed
qed

lemma const_at_lift:
  "const_at (lift_layer L) z = kb4_embed (const_at L z)"
proof -
  have entries:
    "sum_list
       (map snd
         (filter (\<lambda>(i,c). i = z)
           (map (\<lambda>(i,c). (i, kb4_embed c)) xs))) =
     kb4_embed
       (sum_list (map snd (filter (\<lambda>(i,c). i = z) xs)))"
    for xs :: "(nat \<times> koala_bear) list"
  proof (induction xs)
    case Nil
    show ?case by simp
  next
    case (Cons x xs)
    obtain i c where x: "x = (i,c)" by (cases x)
    show ?case using Cons.IH by (simp add: x)
  qed
  have exact:
    "sum_list
       (map snd
         (filter (\<lambda>(i,c). i = z)
           (map (\<lambda>(i,c). (i, kb4_embed c)) (layer_consts L)))) =
     kb4_embed
       (sum_list
         (map snd (filter (\<lambda>(i,c). i = z) (layer_consts L))))"
    by (rule entries[of "layer_consts L"])
  show ?thesis
    unfolding const_at_def
    using exact by (simp add: lift_layer_def)
qed

lemma layer_width_lift [simp]: "layer_width (lift_layer L) = layer_width L"
  by (simp add: layer_width_def lift_layer_def)

lemma layer_eval_embed:
  assumes wf: "wf_layer (length below) L"
  shows "layer_eval (lift_layer L) (map kb4_embed below) =
         map kb4_embed (layer_eval L below)"
proof (rule nth_equalityI)
  show "length (layer_eval (lift_layer L) (map kb4_embed below)) =
        length (map kb4_embed (layer_eval L below))" by simp
next
  fix z assume z:
    "z < length (layer_eval (lift_layer L) (map kb4_embed below))"
  have z_eval: "z < length (layer_eval L below)"
    using z by simp
  have z_base: "z < layer_width L"
    using z_eval by simp
  have z_lift: "z < layer_width (lift_layer L)"
    using z_base by simp
  have gates:
    "g \<in> set (layer_gates L) \<Longrightarrow>
      g_in1 g < length below \<and> g_in2 g < length below" for g
    using wf unfolding wf_layer_def wf_gate_def by blast
  have lifted_nth:
    "layer_eval (lift_layer L) (map kb4_embed below) ! z =
      const_at (lift_layer L) z +
      sum_list
        (map (\<lambda>g. gate_contrib g (map kb4_embed below))
          (filter (\<lambda>g. g_out g = z) (layer_gates (lift_layer L))))"
    by (rule layer_eval_nth[OF z_lift])
  have base_nth:
    "layer_eval L below ! z =
      const_at L z +
      sum_list
        (map (\<lambda>g. gate_contrib g below)
          (filter (\<lambda>g. g_out g = z) (layer_gates L)))"
    by (rule layer_eval_nth[OF z_base])
  have sum_exact:
    "sum_list
       (map (\<lambda>g. gate_contrib g (map kb4_embed below))
         (filter (\<lambda>g. g_out g = z)
           (map lift_gate (layer_gates L)))) =
     kb4_embed
       (sum_list
         (map (\<lambda>g. gate_contrib g below)
           (filter (\<lambda>g. g_out g = z) (layer_gates L))))"
    by (rule gate_contrib_sum_lift[OF gates])
  have sum_lift:
    "sum_list
       (map (\<lambda>g. gate_contrib g (map kb4_embed below))
         (filter (\<lambda>g. g_out g = z) (layer_gates (lift_layer L)))) =
     kb4_embed
       (sum_list
         (map (\<lambda>g. gate_contrib g below)
           (filter (\<lambda>g. g_out g = z) (layer_gates L))))"
    using sum_exact by (simp add: lift_layer_def)
  from lifted_nth have first_eval:
    "layer_eval (lift_layer L) (map kb4_embed below) ! z =
      kb4_embed (const_at L z) +
      kb4_embed
        (sum_list
          (map (\<lambda>g. gate_contrib g below)
           (filter (\<lambda>g. g_out g = z) (layer_gates L))))"
    using const_at_lift sum_lift by simp
  have partial:
    "layer_eval (lift_layer L) (map kb4_embed below) ! z =
      kb4_embed (layer_eval L below ! z)"
  proof -
    have "layer_eval (lift_layer L) (map kb4_embed below) ! z =
        kb4_embed (const_at L z) +
        kb4_embed
          (sum_list
            (map (\<lambda>g. gate_contrib g below)
              (filter (\<lambda>g. g_out g = z) (layer_gates L))))"
      by (rule first_eval)
    also have "... = kb4_embed
        (const_at L z +
          sum_list
            (map (\<lambda>g. gate_contrib g below)
              (filter (\<lambda>g. g_out g = z) (layer_gates L))))"
      by simp
    also have "... = kb4_embed (layer_eval L below ! z)"
      using base_nth by simp
    finally show ?thesis .
  qed
  from partial z_eval show
    "layer_eval (lift_layer L) (map kb4_embed below) ! z =
      map kb4_embed (layer_eval L below) ! z"
    by simp
qed

lemma wf_layer_lift [simp]:
  "wf_layer n (lift_layer L) \<longleftrightarrow> wf_layer n L"
proof -
  have gate_wf:
    "wf_gate (layer_width (lift_layer L)) n (lift_gate g) \<longleftrightarrow>
     wf_gate (layer_width L) n g" for g
    by (simp add: wf_gate_def)
  have const_set:
    "set (layer_consts (lift_layer L)) =
      (\<lambda>(i,c). (i, kb4_embed c)) ` set (layer_consts L)"
    by (simp add: lift_layer_def)
  show ?thesis
  proof
    assume lifted: "wf_layer n (lift_layer L)"
    have lifted_gates:
      "\<forall>g \<in> set (layer_gates (lift_layer L)).
        wf_gate (layer_width (lift_layer L)) n g"
      using lifted unfolding wf_layer_def by blast
    have lifted_consts:
      "\<forall>(w,c) \<in> set (layer_consts (lift_layer L)).
        w < layer_width (lift_layer L)"
      using lifted unfolding wf_layer_def by blast
    show "wf_layer n L"
      unfolding wf_layer_def
    proof (intro conjI)
      show "\<forall>g \<in> set (layer_gates L).
        wf_gate (layer_width L) n g"
      proof (intro ballI)
        fix g
        assume member: "g \<in> set (layer_gates L)"
        have "lift_gate g \<in> set (layer_gates (lift_layer L))"
          using member by (simp add: lift_layer_def)
        with lifted_gates have
          "wf_gate (layer_width (lift_layer L)) n (lift_gate g)"
          by blast
        with gate_wf show "wf_gate (layer_width L) n g" by blast
      qed
      show "\<forall>(w,c) \<in> set (layer_consts L). w < layer_width L"
      proof clarify
        fix w c
        assume member: "(w,c) \<in> set (layer_consts L)"
        have mapped:
          "(\<lambda>(i,c). (i, kb4_embed c)) (w,c) = (w, kb4_embed c)"
          by simp
        have image_member:
          "(\<lambda>(i,c). (i, kb4_embed c)) (w,c) \<in>
            (\<lambda>(i,c). (i, kb4_embed c)) ` set (layer_consts L)"
          by (rule imageI[OF member])
        have lifted_member:
          "(w, kb4_embed c) \<in> set (layer_consts (lift_layer L))"
          using const_set image_member mapped by simp
        from lifted_consts lifted_member have
          "w < layer_width (lift_layer L)" by blast
        then show "w < layer_width L" by simp
      qed
    qed
  next
    assume base: "wf_layer n L"
    have base_gates:
      "\<forall>g \<in> set (layer_gates L). wf_gate (layer_width L) n g"
      using base unfolding wf_layer_def by blast
    have base_consts:
      "\<forall>(w,c) \<in> set (layer_consts L). w < layer_width L"
      using base unfolding wf_layer_def by blast
    show "wf_layer n (lift_layer L)"
      unfolding wf_layer_def
    proof (intro conjI)
      show "\<forall>g \<in> set (layer_gates (lift_layer L)).
        wf_gate (layer_width (lift_layer L)) n g"
      proof (intro ballI)
        fix g'
        assume member: "g' \<in> set (layer_gates (lift_layer L))"
        then obtain g where original: "g \<in> set (layer_gates L)"
          and lifted_gate: "g' = lift_gate g"
          by (auto simp: lift_layer_def)
        from base_gates original have "wf_gate (layer_width L) n g"
          by blast
        with gate_wf lifted_gate show
          "wf_gate (layer_width (lift_layer L)) n g'" by blast
      qed
      show "\<forall>(w,c) \<in> set (layer_consts (lift_layer L)).
        w < layer_width (lift_layer L)"
      proof clarify
        fix w c'
        assume member:
          "(w,c') \<in> set (layer_consts (lift_layer L))"
        have image_member:
          "(w,c') \<in>
            (\<lambda>(i,c). (i, kb4_embed c)) ` set (layer_consts L)"
          using const_set member by simp
        then obtain p where original_p: "p \<in> set (layer_consts L)"
          and mapped:
            "(w,c') = (\<lambda>(i,c). (i, kb4_embed c)) p"
          by (rule imageE)
        obtain w0 c where p: "p = (w0,c)" by (cases p)
        have w0: "w0 = w" using mapped by (simp add: p)
        have original: "(w,c) \<in> set (layer_consts L)"
          using original_p by (simp add: p w0)
        from base_consts original have "w < layer_width L" by blast
        then show "w < layer_width (lift_layer L)" by simp
      qed
    qed
  qed
qed

lemma false_output_preserved:
  assumes wf: "wf_layer (length below) L"
    and idx: "idx < length (layer_eval L below)"
    and bad: "outs idx \<noteq> layer_eval L below ! idx"
  shows "(kb4_embed \<circ> outs) idx \<noteq>
         layer_eval (lift_layer L) (map kb4_embed below) ! idx"
proof -
  have eval:
    "layer_eval (lift_layer L) (map kb4_embed below) =
       map kb4_embed (layer_eval L below)"
    by (rule layer_eval_embed[OF wf])
  have mapped:
    "layer_eval (lift_layer L) (map kb4_embed below) ! idx =
       kb4_embed (layer_eval L below ! idx)"
    using idx eval by simp
  have embedded_bad:
    "kb4_embed (outs idx) \<noteq> kb4_embed (layer_eval L below ! idx)"
  proof
    assume eq:
      "kb4_embed (outs idx) = kb4_embed (layer_eval L below ! idx)"
    from kb4_embed_inj eq have
      "outs idx = layer_eval L below ! idx"
      by (rule injD)
    with bad show False by contradiction
  qed
  show ?thesis
  proof
    assume eq:
      "(kb4_embed \<circ> outs) idx =
       layer_eval (lift_layer L) (map kb4_embed below) ! idx"
    have "kb4_embed (outs idx) =
          kb4_embed (layer_eval L below ! idx)"
      using eq mapped by simp
    with embedded_bad show False by contradiction
  qed
qed

end
