(*
  Title:   Compiler_Instance.thy
  Session: SMT_Circuit_Compiler_Correctness (SMT-specific layer)

  Non-vacuity witness for the compiler model: the
  compiler_model locale - and with it every Theorem A statement - is
  instantiated over the PRODUCTION wire field (KoalaBear) with

    - a transparent linear "hash" pair (hl/hn are one-lane affine maps;
      Theorem A needs NO hash strength, so a linear instance is
      the honest minimal witness),
    - depth 1 (the key-bit multiplexer and the compression chain are
      actually exercised - the instance is not degenerate),
    - an ACTUAL evaluation-stack layer: a concrete gate list (Lin/Mul
      gates emitted from quadratic wire descriptors) whose layer_eval
      provably equals the specification vector ev_ro/ev_up.  This
      discharges the stack_spec_ro/up assumptions - the assumptions
      whose satisfiability the power-of-two padding of the specification
      vectors restored.

  Activation examples: a concrete Membership operation round-trips
  through theorem_A_completeness / theorem_A_soundness, and a mismatched
  root pair is semantically unsatisfiable (the nosem premise of
  Theorem C, consumed by Composition_Instance).
*)

theory Compiler_Instance
  imports Compiler_Correctness KoalaBear_Field
begin

declare One_nat_def [simp del]
  \<comment> \<open>\<open>One_nat_def\<close> (\<open>1 = Suc 0\<close>) is a default simp rule, and it rewrites the
     NUMERAL ARGUMENTS of the interpreted locale constants: a goal about
     \<open>compiler_model_base.ev_tag kb_params 1\<close> silently becomes one about
     \<open>\<dots> kb_params (Suc 0)\<close>, after which none of the \<open>kbc_base.*_def\<close> equations
     - whose left-hand sides carry the literal \<open>1\<close> that the interpretation
     supplied for \<open>W\<close> - can ever match, and every layout lemma fails with an
     unsolved goal that LOOKS identical to its own definition.  It is
     re-enabled locally where \<open>Suc\<close>-shaped list/index arithmetic needs it\<close>

section \<open>The KoalaBear toy hash pair and representations\<close>

fun kb_pay :: "koala_bear leaf_state \<Rightarrow> koala_bear" where
  "kb_pay Empty = 0"
| "kb_pay (Occupied v) = v"
| "kb_pay Tombstone = 0"

definition kb_h_leaf :: "koala_bear leaf_state \<Rightarrow> koala_bear" where
  "kb_h_leaf lf = leaf_tag_val lf + 3 * kb_pay lf"

definition kb_h_node :: "koala_bear \<Rightarrow> koala_bear \<Rightarrow> koala_bear" where
  "kb_h_node a b = a + 2 * b"

definition kb_digest_repr :: "koala_bear \<Rightarrow> koala_bear list" where
  "kb_digest_repr d = [d]"

definition kb_leaf_repr :: "koala_bear leaf_state \<Rightarrow> koala_bear list" where
  "kb_leaf_repr lf = [leaf_tag_val lf, kb_pay lf]"

definition kb_hl :: "koala_bear list \<Rightarrow> koala_bear list" where
  "kb_hl xs = [xs ! 0 + 3 * xs ! 1]"

definition kb_hn :: "koala_bear list \<Rightarrow> koala_bear list \<Rightarrow> koala_bear list" where
  "kb_hn a b = [a ! 0 + 2 * b ! 0]"

definition kb_params :: smt_params where
  "kb_params = \<lparr> depth = 1, leaf_max_fields = 4 \<rparr>"

interpretation kbc_base: compiler_model_base
  kb_params kb_h_leaf kb_h_node 1 2 kb_digest_repr kb_leaf_repr kb_hl kb_hn
  by unfold_locales
     (auto simp add: kb_digest_repr_def kb_leaf_repr_def kb_hl_def kb_hn_def
                     kb_h_leaf_def kb_h_node_def)

lemma kbc_dd [simp]: "depth kb_params = 1"
  by (simp add: kb_params_def)

section \<open>Quadratic wire descriptors and their gate layers\<close>

text \<open>A wire is a linear combination of below-wires plus a linear
  combination of products of below-wire pairs - the exact shape of the
  instance's stack components (affine hashes over key-bit muxes).\<close>

type_synonym 'f qwire = "('f \<times> nat) list \<times> ('f \<times> nat \<times> nat) list"

definition qw_sem :: "'f::comm_ring_1 list \<Rightarrow> 'f qwire \<Rightarrow> 'f" where
  "qw_sem below w =
     (\<Sum>(c, i) \<leftarrow> fst w. c * below ! i)
   + (\<Sum>(c, i, j) \<leftarrow> snd w. c * (below ! i * below ! j))"

definition qw_gates :: "nat \<Rightarrow> 'f::comm_ring_1 qwire \<Rightarrow> 'f gate list" where
  "qw_gates z w =
     map (\<lambda>(c, i). \<lparr> g_kind = GLin, g_out = z, g_in1 = i, g_in2 = i, g_coeff = c \<rparr>) (fst w)
   @ map (\<lambda>(c, i, j). \<lparr> g_kind = GMul, g_out = z, g_in1 = i, g_in2 = j, g_coeff = c \<rparr>) (snd w)"

definition mk_q_layer :: "'f::comm_ring_1 qwire list \<Rightarrow> 'f layer" where
  "mk_q_layer ws =
     \<lparr> layer_width_bits = length ws,
       layer_gates = concat (map (\<lambda>(z, w). qw_gates z w) (List.enumerate 0 ws)),
       layer_consts = [] \<rparr>"

lemma qw_gates_out: "g \<in> set (qw_gates z w) \<Longrightarrow> g_out g = z"
  by (auto simp add: qw_gates_def)

lemma filter_qw_gates_same:
  "filter (\<lambda>g. g_out g = z) (qw_gates z w) = qw_gates z w"
  by (auto simp add: filter_id_conv dest: qw_gates_out)

lemma filter_qw_gates_other:
  "k \<noteq> z \<Longrightarrow> filter (\<lambda>g. g_out g = z) (qw_gates k w) = []"
  by (auto simp add: filter_empty_conv dest: qw_gates_out)

lemma filter_enumerate_qw_gates_miss:
  assumes "z < n \<or> n + length ws \<le> z"
  shows "filter (\<lambda>g. g_out g = z)
           (concat (map (\<lambda>(k, w). qw_gates k w) (List.enumerate n ws))) = []"
  using assms
proof (induction ws arbitrary: n)
  case Nil then show ?case by simp
next
  case (Cons w ws)
  then have "z \<noteq> n" and rest: "z < Suc n \<or> Suc n + length ws \<le> z" by auto
  with Cons.IH[OF rest] show ?case
    by (simp add: filter_qw_gates_other)
qed

lemma filter_enumerate_qw_gates:
  assumes "n \<le> z" "z < n + length ws"
  shows "filter (\<lambda>g. g_out g = z)
           (concat (map (\<lambda>(k, w). qw_gates k w) (List.enumerate n ws)))
         = (qw_gates z (ws ! (z - n)) :: 'f::comm_ring_1 gate list)"
  using assms
proof (induction ws arbitrary: n)
  case Nil then show ?case by simp
next
  case (Cons w ws)
  show ?case
  proof (cases "n = z")
    case True
    have "filter (\<lambda>g. g_out g = z)
            (concat (map (\<lambda>(k, w). qw_gates k w) (List.enumerate (Suc n) ws))) = []"
      using True by (intro filter_enumerate_qw_gates_miss) simp
    with True show ?thesis
      by (simp add: filter_qw_gates_same)
  next
    case False
    with Cons.prems have le: "Suc n \<le> z" and lt: "z < Suc n + length ws" by auto
    have ih: "filter (\<lambda>g. g_out g = z)
        (concat (map (\<lambda>(k, w). qw_gates k w) (List.enumerate (Suc n) ws)))
      = (qw_gates z (ws ! (z - Suc n)) :: 'f gate list)"
      by (rule Cons.IH[OF le lt])
    have idx: "(w # ws) ! (z - n) = ws ! (z - Suc n)"
      using le by (simp add: Suc_diff_le nth_Cons' One_nat_def)
    \<comment> \<open>one of the few places that wants \<open>One_nat_def\<close> back: the goal pairs
       \<open>z - (n + 1)\<close> against \<open>z - Suc n\<close>\<close>
    from False show ?thesis
      by (simp add: filter_qw_gates_other ih idx)
  qed
qed

lemma qw_gates_contrib_sum:
  "sum_list (map (\<lambda>g. gate_contrib g below) (qw_gates z w)) = qw_sem below w"
  by (simp add: qw_gates_def qw_sem_def gate_contrib_def comp_def case_prod_unfold
                mult.assoc)
    \<comment> \<open>\<open>case_prod_unfold\<close>, not \<open>case_prod_beta\<close>: under \<open>map\<close> the pair pattern
       is ETA-CONTRACTED (\<open>case_prod f\<close>, no argument), and the \<open>beta\<close> rule's
       left-hand side is an APPLIED \<open>case_prod f p\<close>, so it never matches\<close>

lemma mk_q_layer_width: "layer_width (mk_q_layer ws) = 2 ^ length ws"
  by (simp add: mk_q_layer_def layer_width_def)

lemma mk_q_layer_eval_in:
  assumes z: "z < length ws"
  shows "layer_eval (mk_q_layer ws) below ! z = qw_sem below (ws ! z)"
proof -
  have zw: "z < layer_width (mk_q_layer ws)"
    unfolding mk_q_layer_width by (meson z less_exp less_trans)
  have flt: "filter (\<lambda>g. g_out g = z) (layer_gates (mk_q_layer ws))
             = qw_gates z (ws ! z)"
    using filter_enumerate_qw_gates[of 0 z ws] z
    by (simp add: mk_q_layer_def)
  have cst: "const_at (mk_q_layer ws) z = 0"
    by (simp add: mk_q_layer_def const_at_def)
  show ?thesis
    using layer_eval_nth[OF zw]
    by (simp add: flt cst qw_gates_contrib_sum)
qed

lemma mk_q_layer_eval_pad:
  fixes below :: "'f::comm_ring_1 list"
  assumes ge: "length ws \<le> z"
      and zw: "z < layer_width (mk_q_layer ws :: 'f layer)"
  shows "layer_eval (mk_q_layer ws) below ! z = 0"
proof -
  have flt: "filter (\<lambda>g. g_out g = z) (layer_gates (mk_q_layer ws :: 'f layer)) = []"
    using filter_enumerate_qw_gates_miss[of z 0 ws] ge
    by (simp add: mk_q_layer_def)
  have cst: "const_at (mk_q_layer ws :: 'f layer) z = 0"
    by (simp add: mk_q_layer_def const_at_def)
  show ?thesis
    by (simp add: layer_eval_nth[OF zw] flt cst)
qed

section \<open>Small list-segment computation lemmas\<close>

lemma seg_one:
  assumes "a < length xs"
  shows "seg a 1 xs = [xs ! a]"
proof -
  from assms have "drop a xs = xs ! a # drop (Suc a) xs"
    by (simp add: Cons_nth_drop_Suc)
  then show ?thesis by (simp add: seg_def One_nat_def)
qed

lemma seg_two:
  assumes "Suc a < length xs"
  shows "seg a 2 xs = [xs ! a, xs ! Suc a]"
proof -
  from assms have "drop a xs = xs ! a # drop (Suc a) xs"
    by (simp add: Cons_nth_drop_Suc)
  moreover from assms have "drop (Suc a) xs = xs ! Suc a # drop (Suc (Suc a)) xs"
    by (simp add: Cons_nth_drop_Suc)
  ultimately have "drop a xs = xs ! a # xs ! Suc a # drop (Suc (Suc a)) xs"
    by simp
  then show ?thesis by (simp add: seg_def numeral_2_eq_2)
qed

section \<open>The concrete evaluation stacks (depth 1, one-lane digests)\<close>

text \<open>Read-only layout at W = 1, L = 2, dd = 1:
  lp = wires 0-1, \<open>acc_0\<close> = 2, \<open>acc_1\<close> = 3, \<open>sib_0\<close> = 4, \<open>kb_0\<close> = 5, root = 6,
  vd = 7; \<open>ro_width\<close> = 8.  Stack output slots (\<open>ev_ro_core\<close> order):
  hl = 0, \<open>hn_0\<close> = 1, \<open>acc_0\<close> = 2, \<open>acc_1\<close> = 3, \<open>kb_0\<close> = 4, root = 5, vd = 6,
  tag = 7; \<open>ev_ro_len\<close> = 8.\<close>

definition kb_ro_stack_desc :: "koala_bear qwire list" where
  "kb_ro_stack_desc =
     [ ([(1, 0), (3, 1)], []),
       ([(1, 2), (2, 4)], [(1, 5, 2), (- 1, 5, 4)]),
       ([(1, 2)], []),
       ([(1, 3)], []),
       ([(1, 5)], []),
       ([(1, 6)], []),
       ([(1, 7)], []),
       ([(1, 0)], []) ]"

text \<open>Update layout at W = 1, L = 2, dd = 1:
  lp = 0-1, lp2 = 2-3, \<open>acc_0\<close> = 4, \<open>acc_1\<close> = 5, \<open>acc2_0\<close> = 6, \<open>acc2_1\<close> = 7,
  \<open>sib_0\<close> = 8, \<open>kb_0\<close> = 9, root = 10, root2 = 11, vd = 12; \<open>up_width\<close> = 13.
  Stack output slots (\<open>ev_up_core\<close> order): hl = 0, hl2 = 1, \<open>hn_0\<close> = 2,
  \<open>hn2_0\<close> = 3, \<open>acc_0\<close> = 4, \<open>acc_1\<close> = 5, \<open>acc2_0\<close> = 6, \<open>acc2_1\<close> = 7, \<open>kb_0\<close> = 8,
  root = 9, root2 = 10, vd = 11; \<open>ev_up_len\<close> = 12.\<close>

definition kb_up_stack_desc :: "koala_bear qwire list" where
  "kb_up_stack_desc =
     [ ([(1, 0), (3, 1)], []),
       ([(1, 2), (3, 3)], []),
       ([(1, 4), (2, 8)], [(1, 9, 4), (- 1, 9, 8)]),
       ([(1, 6), (2, 8)], [(1, 9, 6), (- 1, 9, 8)]),
       ([(1, 4)], []),
       ([(1, 5)], []),
       ([(1, 6)], []),
       ([(1, 7)], []),
       ([(1, 9)], []),
       ([(1, 10)], []),
       ([(1, 11)], []),
       ([(1, 12)], []) ]"

definition kb_stack :: "op_kind \<Rightarrow> koala_bear layer list" where
  "kb_stack k =
     (if k = KUpdate then [mk_q_layer kb_up_stack_desc]
      else [mk_q_layer kb_ro_stack_desc])"

subsection \<open>Layout arithmetic at the concrete parameters\<close>

lemma kb_ro_offsets [simp]:
  "kbc_base.ro_lp = 0" "kbc_base.ro_acc l = 2 + l" "kbc_base.ro_sib l = 4 + l"
  "kbc_base.ro_kb l = 5 + l" "kbc_base.ro_root = 6" "kbc_base.ro_vd = 7"
  "kbc_base.ro_width = 8"
  by (simp_all add: kbc_base.ro_lp_def kbc_base.ro_acc_def kbc_base.ro_sib_def
                    kbc_base.ro_kb_def kbc_base.ro_root_def kbc_base.ro_vd_def
                    kbc_base.ro_width_def)

lemma kb_up_offsets [simp]:
  "kbc_base.up_lp = 0" "kbc_base.up_lp2 = 2" "kbc_base.up_acc l = 4 + l"
  "kbc_base.up_acc2 l = 6 + l" "kbc_base.up_sib l = 8 + l" "kbc_base.up_kb l = 9 + l"
  "kbc_base.up_root = 10" "kbc_base.up_root2 = 11" "kbc_base.up_vd = 12"
  "kbc_base.up_width = 13"
  by (simp_all add: kbc_base.up_lp_def kbc_base.up_lp2_def kbc_base.up_acc_def
                    kbc_base.up_acc2_def kbc_base.up_sib_def kbc_base.up_kb_def
                    kbc_base.up_root_def kbc_base.up_root2_def kbc_base.up_vd_def
                    kbc_base.up_width_def)

lemma kb_ev_slots [simp]:
  "kbc_base.ev_hl = 0" "kbc_base.ev_hn l = 1 + l" "kbc_base.ev_acc l = 2 + l"
  "kbc_base.ev_kb l = 4 + l" "kbc_base.ev_root = 5" "kbc_base.ev_vd = 6"
  "kbc_base.ev_tag = 7"
  by (simp_all add: kbc_base.ev_hl_def kbc_base.ev_hn_def kbc_base.ev_acc_def
                    kbc_base.ev_kb_def kbc_base.ev_root_def kbc_base.ev_vd_def
                    kbc_base.ev_tag_def)

lemma kb_ev2_slots [simp]:
  "kbc_base.ev2_hl = 0" "kbc_base.ev2_hl2 = 1" "kbc_base.ev2_hn l = 2 + l"
  "kbc_base.ev2_hn2 l = 3 + l" "kbc_base.ev2_acc l = 4 + l"
  "kbc_base.ev2_acc2 l = 6 + l" "kbc_base.ev2_kb l = 8 + l"
  "kbc_base.ev2_root = 9" "kbc_base.ev2_root2 = 10" "kbc_base.ev2_vd = 11"
  by (simp_all add: kbc_base.ev2_hl_def kbc_base.ev2_hl2_def kbc_base.ev2_hn_def
                    kbc_base.ev2_hn2_def kbc_base.ev2_acc_def kbc_base.ev2_acc2_def
                    kbc_base.ev2_kb_def kbc_base.ev2_root_def kbc_base.ev2_root2_def
                    kbc_base.ev2_vd_def)

lemma kb_ev_ro_len [simp]: "kbc_base.ev_ro_len = 8"
  by (simp add: kbc_base.ev_ro_len_def)

lemma kb_ev_up_len [simp]: "kbc_base.ev_up_len = 12"
  by (simp add: kbc_base.ev_up_len_def)

lemma kb_iwb_ro [simp]: "k \<noteq> KUpdate \<Longrightarrow> kbc_base.iwb k = 8"
  by (cases k) (simp_all add: kbc_base.iwb_def)

lemma kb_iwb_up [simp]: "kbc_base.iwb KUpdate = 13"
  by (simp add: kbc_base.iwb_def)

subsection \<open>The explicit specification vectors at the concrete layout\<close>

lemma kb_ev_ro_core_explicit:
  assumes len: "(8 :: nat) \<le> length xs"
  shows "kbc_base.ev_ro_core xs =
    [ xs ! 0 + 3 * xs ! 1,
      (xs ! 2 + xs ! 5 * (xs ! 4 - xs ! 2)) + 2 * (xs ! 4 + xs ! 5 * (xs ! 2 - xs ! 4)),
      xs ! 2, xs ! 3, xs ! 5, xs ! 6, xs ! 7, xs ! 0 ]"
  using len
  unfolding kbc_base.ev_ro_core_def kbc_base.ro_mxl_def kbc_base.ro_mxr_def
            kb_ro_offsets kbc_dd
  by (simp add: kb_hl_def kb_hn_def mux_left_def mux_right_def
                seg_one seg_two upt_rec)
     (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)

lemma kb_ev_up_core_explicit:
  assumes len: "(13 :: nat) \<le> length xs"
  shows "kbc_base.ev_up_core xs =
    [ xs ! 0 + 3 * xs ! 1,
      xs ! 2 + 3 * xs ! 3,
      (xs ! 4 + xs ! 9 * (xs ! 8 - xs ! 4)) + 2 * (xs ! 8 + xs ! 9 * (xs ! 4 - xs ! 8)),
      (xs ! 6 + xs ! 9 * (xs ! 8 - xs ! 6)) + 2 * (xs ! 8 + xs ! 9 * (xs ! 6 - xs ! 8)),
      xs ! 4, xs ! 5, xs ! 6, xs ! 7, xs ! 9, xs ! 10, xs ! 11, xs ! 12 ]"
  using len
  unfolding kbc_base.ev_up_core_def kbc_base.up_mxl_def kbc_base.up_mxr_def
            kb_up_offsets kbc_dd
  by (simp add: kb_hl_def kb_hn_def mux_left_def mux_right_def
                seg_one seg_two upt_rec)
     (simp add: One_nat_def numeral_2_eq_2 numeral_3_eq_3)

subsection \<open>The stack layers compute the specification vectors\<close>

lemma kb_ro_stack_eval:
  assumes len: "length xs = 2 ^ 8"
  shows "layer_eval (mk_q_layer kb_ro_stack_desc) xs = kbc_base.ev_ro xs"
proof (rule nth_equalityI)
  have len8: "(8 :: nat) \<le> length xs" using len by simp
  have core: "kbc_base.ev_ro_core xs =
    [ xs ! 0 + 3 * xs ! 1,
      (xs ! 2 + xs ! 5 * (xs ! 4 - xs ! 2)) + 2 * (xs ! 4 + xs ! 5 * (xs ! 2 - xs ! 4)),
      xs ! 2, xs ! 3, xs ! 5, xs ! 6, xs ! 7, xs ! 0 ]"
    by (rule kb_ev_ro_core_explicit[OF len8])
  have lcore: "length (kbc_base.ev_ro_core xs) = 8" by (simp add: core)
  show leq: "length (layer_eval (mk_q_layer kb_ro_stack_desc) xs)
             = length (kbc_base.ev_ro xs)"
    by (simp add: mk_q_layer_width layer_width_def mk_q_layer_def
                  kb_ro_stack_desc_def kbc_base.ev_ro_def length_pad_to lcore)
  fix z assume z: "z < length (layer_eval (mk_q_layer kb_ro_stack_desc) xs)"
  then have z256: "z < 2 ^ 8"
    by (simp add: mk_q_layer_width layer_width_def mk_q_layer_def kb_ro_stack_desc_def)
  show "layer_eval (mk_q_layer kb_ro_stack_desc) xs ! z = kbc_base.ev_ro xs ! z"
  proof (cases "z < 8")
    case True
    have lhs: "layer_eval (mk_q_layer kb_ro_stack_desc) xs ! z
               = qw_sem xs (kb_ro_stack_desc ! z)"
      by (rule mk_q_layer_eval_in) (simp add: kb_ro_stack_desc_def True One_nat_def [symmetric])
    have rhs: "kbc_base.ev_ro xs ! z = kbc_base.ev_ro_core xs ! z"
      unfolding kbc_base.ev_ro_def
      by (rule pad_to_nth) (simp add: lcore True)
    have "z \<in> {0, 1, 2, 3, 4, 5, 6, 7}" using True by auto
    then show ?thesis
      unfolding lhs rhs core
      by (elim insertE emptyE)
         (simp_all add: kb_ro_stack_desc_def qw_sem_def algebra_simps)
  next
    case False
    have lhs: "layer_eval (mk_q_layer kb_ro_stack_desc) xs ! z = 0"
      by (rule mk_q_layer_eval_pad)
         (use False z in \<open>simp_all add: kb_ro_stack_desc_def\<close>)
    have "kbc_base.ev_ro xs ! z = (kbc_base.ev_ro_core xs @ replicate (2 ^ 8 - 8) 0) ! z"
      by (simp add: kbc_base.ev_ro_def pad_to_def lcore)
    also have "\<dots> = replicate (2 ^ 8 - 8) 0 ! (z - 8)"
      using False by (simp add: nth_append lcore)
    also have "\<dots> = 0"
      using z256 False by (intro nth_replicate) simp
    finally show ?thesis by (simp add: lhs)
  qed
qed

lemma kb_up_stack_eval:
  assumes len: "length xs = 2 ^ 13"
  shows "layer_eval (mk_q_layer kb_up_stack_desc) xs = kbc_base.ev_up xs"
proof (rule nth_equalityI)
  have len13: "(13 :: nat) \<le> length xs" using len by simp
  have core: "kbc_base.ev_up_core xs =
    [ xs ! 0 + 3 * xs ! 1,
      xs ! 2 + 3 * xs ! 3,
      (xs ! 4 + xs ! 9 * (xs ! 8 - xs ! 4)) + 2 * (xs ! 8 + xs ! 9 * (xs ! 4 - xs ! 8)),
      (xs ! 6 + xs ! 9 * (xs ! 8 - xs ! 6)) + 2 * (xs ! 8 + xs ! 9 * (xs ! 6 - xs ! 8)),
      xs ! 4, xs ! 5, xs ! 6, xs ! 7, xs ! 9, xs ! 10, xs ! 11, xs ! 12 ]"
    by (rule kb_ev_up_core_explicit[OF len13])
  have lcore: "length (kbc_base.ev_up_core xs) = 12" by (simp add: core)
  show "length (layer_eval (mk_q_layer kb_up_stack_desc) xs)
        = length (kbc_base.ev_up xs)"
    by (simp add: mk_q_layer_width layer_width_def mk_q_layer_def
                  kb_up_stack_desc_def kbc_base.ev_up_def length_pad_to lcore)
  fix z assume z: "z < length (layer_eval (mk_q_layer kb_up_stack_desc) xs)"
  then have z4096: "z < 2 ^ 12"
    by (simp add: mk_q_layer_width layer_width_def mk_q_layer_def kb_up_stack_desc_def)
  show "layer_eval (mk_q_layer kb_up_stack_desc) xs ! z = kbc_base.ev_up xs ! z"
  proof (cases "z < 12")
    case True
    have lhs: "layer_eval (mk_q_layer kb_up_stack_desc) xs ! z
               = qw_sem xs (kb_up_stack_desc ! z)"
      by (rule mk_q_layer_eval_in) (simp add: kb_up_stack_desc_def True One_nat_def [symmetric])
    have rhs: "kbc_base.ev_up xs ! z = kbc_base.ev_up_core xs ! z"
      unfolding kbc_base.ev_up_def
      by (rule pad_to_nth) (simp add: lcore True)
    have "z \<in> {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}" using True by (auto; presburger)
    then show ?thesis
      unfolding lhs rhs core
      by (elim insertE emptyE)
         (simp_all add: kb_up_stack_desc_def qw_sem_def algebra_simps)
  next
    case False
    have lhs: "layer_eval (mk_q_layer kb_up_stack_desc) xs ! z = 0"
      by (rule mk_q_layer_eval_pad)
         (use False z in \<open>simp_all add: kb_up_stack_desc_def\<close>)
    have "kbc_base.ev_up xs ! z = (kbc_base.ev_up_core xs @ replicate (2 ^ 12 - 12) 0) ! z"
      by (simp add: kbc_base.ev_up_def pad_to_def lcore)
    also have "\<dots> = replicate (2 ^ 12 - 12) 0 ! (z - 12)"
      using False by (simp add: nth_append lcore)
    also have "\<dots> = 0"
      using z4096 False by (intro nth_replicate) simp
    finally show ?thesis by (simp add: lhs)
  qed
qed

section \<open>The compiler model is inhabited over KoalaBear\<close>

lemma compiler_model_kb:
  "compiler_model kb_params kb_h_leaf kb_h_node 1 2
     kb_digest_repr kb_leaf_repr kb_hl kb_hn kb_stack"
    \<comment> \<open>\<open>unfold_locales\<close> discharges the entire \<open>compiler_model_base\<close> part from
       the \<open>kbc_base\<close> interpretation above; exactly the two \<open>stack_spec\<close>
       obligations remain\<close>
proof (unfold_locales)
  fix k :: op_kind and xs :: "koala_bear list"
  assume k: "k \<noteq> KUpdate" and len: "length xs = kbc_base.ivlen k"
  have "length xs = 2 ^ 8"
    using len k by (simp add: kbc_base.ivlen_def)
  then show "foldr layer_eval (kb_stack k) xs = kbc_base.ev_ro xs"
    using k by (simp add: kb_stack_def kb_ro_stack_eval)
next
  fix xs :: "koala_bear list"
  assume len: "length xs = kbc_base.ivlen KUpdate"
  have "length xs = 2 ^ 13"
    using len by (simp add: kbc_base.ivlen_def)
  then show "foldr layer_eval (kb_stack KUpdate) xs = kbc_base.ev_up xs"
    by (simp add: kb_stack_def kb_up_stack_eval)
qed

interpretation kbc: compiler_model
  kb_params kb_h_leaf kb_h_node 1 2 kb_digest_repr kb_leaf_repr kb_hl kb_hn kb_stack
  by (rule compiler_model_kb)

section \<open>Activation examples\<close>

text \<open>A concrete valid Membership round-trips through the verifier
  model: completeness accepts it, soundness recovers the semantics.\<close>

definition ex_v :: koala_bear where "ex_v = 5"
definition ex_s :: koala_bear where "ex_s = 7"
definition ex_root :: koala_bear where
  "ex_root = kb_h_node (kb_h_leaf (Occupied ex_v)) ex_s"

lemma ex_smt_valid:
  "kbc_base.smt_valid (Membership 0 ex_v) ex_root ex_root (Occupied ex_v, [ex_s])"
proof -
  have "kbc_base.path_ok (Occupied ex_v) 0 [ex_s] ex_root"
    unfolding kbc_base.path_ok_def
    by (simp add: kbc_base.path_root.simps ex_root_def kb_params_def)
  then show ?thesis by (simp add: kbc_base.smt_valid.simps)
qed

theorem instance_theorem_A_activation:
  "kbc.verifier_accept (Membership 0 ex_v) ex_root ex_root
     (kb_h_leaf (Occupied ex_v)) (Occupied ex_v, [ex_s])"
  using kbc.theorem_A_completeness[OF ex_smt_valid]
  by (simp add: kbc.wit_vd_def)

corollary instance_theorem_A_roundtrip:
  "kbc_base.smt_valid (Membership 0 ex_v) ex_root ex_root (Occupied ex_v, [ex_s])"
  using kbc.theorem_A_soundness[OF instance_theorem_A_activation]
  by (simp add: kbc.canon_witness_def)

text \<open>A mismatched root pair is semantically unsatisfiable - the
  \<open>nosem\<close> premise of Theorem C, discharged concretely.\<close>

lemma ex_nosem:
  "\<not> (\<exists>w. kbc_base.smt_valid (Membership 0 ex_v) ex_root (ex_root + 1) w)"
proof
  assume "\<exists>w. kbc_base.smt_valid (Membership 0 ex_v) ex_root (ex_root + 1) w"
  then obtain lf sb where "kbc_base.smt_valid (Membership 0 ex_v) ex_root (ex_root + 1) (lf, sb)"
    by (metis prod.exhaust)
  then have "ex_root + 1 = ex_root" by (simp add: kbc_base.smt_valid.simps)
  then show False by simp
qed

end
