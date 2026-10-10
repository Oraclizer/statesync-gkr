(*
  Title:   Composition_Instance.thy
  Session: SMT_Circuit_Compiler_Correctness (SMT-specific layer)

  Non-vacuity witness for the COMPOSED pipeline:
  the statesync_gkr_v01 locale - the merge of the compiler model and the
  GKR bridge over ONE challenge field - is instantiated over KoalaBear
  with the AFP mpoly polynomial structure, and Theorem C is ACTIVATED:
  every premise (chain shape, representative, public inputs, semantic
  unsatisfiability) is discharged concretely, yielding the composed
  soundness bound for an actual operation against an actual compiled
  circuit.

  The scenario: an Update whose old/new leaf hashes force incompatible
  root equations (subtracting the two path equations eliminates the
  sibling, leaving 4 = 0, false in KoalaBear) - so NO witness satisfies
  the semantics, while all public-input checks pass.  The representative
  supplied to the chain is the mpoly interpolation of
  Layer_Representative with the width-dependent degree bound
  dbnd = (\<lambda>s. 2 * s).
*)

theory Composition_Instance
  imports Composition Compiler_Instance Leaf_Fold GKR_Protocol.Layer_Representative
begin

declare One_nat_def [simp del]
  \<comment> \<open>as in \<open>Compiler_Instance\<close>: \<open>1 = Suc 0\<close> rewrites the numeral arguments of the
     interpreted locale constants and thereby breaks every \<open>kbc_base.*_def\<close> match\<close>

section \<open>Lemma (b) over the production field\<close>

text \<open>The leaf-hash structure locale is inhabited over KoalaBear: the
  \<open>of_nat\<close>-injectivity-on-bound premise is discharged by the
  concrete field fact that 31 is far below the characteristic, witnessing that the collision
  reduction of lemma (b) applies at the production parameters.\<close>

interpretation kb_leaf_hash: leaf_hash_structure
  "\<lambda>enc :: koala_bear list. leaf_fold enc 31" "\<lambda>p. p" 31
proof
  fix a b assume "a \<le> (31 :: nat)" and "b \<le> (31 :: nat)"
    and "(of_nat a :: koala_bear) = of_nat b"
  then show "a = b"
    by (intro kb_of_nat_inj_on_bound) simp_all
qed simp_all

section \<open>The composed locale is inhabited over KoalaBear + mpoly\<close>

lemma gkr_layer_sumcheck_mpoly:
  "gkr_layer_sumcheck (vars :: 'a::{finite, field} mpoly \<Rightarrow> nat set) total_degree
     (\<lambda>p \<sigma>. insertion (the \<circ> \<sigma>) p) inst"
  by unfold_locales (auto simp add: multi_variate_polynomial_lemmas)

lemma statesync_gkr_v01_kb:
  "statesync_gkr_v01 kb_params kb_h_leaf kb_h_node 1 2
     kb_digest_repr kb_leaf_repr kb_hl kb_hn kb_stack
     (vars :: koala_bear mpoly \<Rightarrow> nat set) total_degree
     (\<lambda>p \<sigma>. insertion (the \<circ> \<sigma>) p) inst"
  by (rule statesync_gkr_v01.intro[OF compiler_model_kb gkr_layer_sumcheck_mpoly])

interpretation kbs: statesync_gkr_v01
  kb_params kb_h_leaf kb_h_node 1 2 kb_digest_repr kb_leaf_repr kb_hl kb_hn kb_stack
  "vars :: koala_bear mpoly \<Rightarrow> nat set" total_degree
  "\<lambda>p \<sigma>. insertion (the \<circ> \<sigma>) p" inst
  by (rule statesync_gkr_v01_kb)

section \<open>The activation scenario\<close>

definition exC_op :: "koala_bear smt_op" where
  "exC_op = Update 0 Empty (Occupied 1)"

definition exC_w :: "koala_bear leaf_state \<times> koala_bear list" where
  "exC_w = (Empty, [0])"

definition exC_vd :: koala_bear where
  "exC_vd = kb_h_leaf (Occupied 1)"

lemma exC_kind [simp]: "kind_of exC_op = KUpdate"
  by (simp add: exC_op_def)

subsection \<open>Semantic unsatisfiability (the nosem premise)\<close>

lemma exC_nosem: "\<not> (\<exists>w'. kbc_base.smt_valid exC_op 0 0 w')"
proof
  assume "\<exists>w'. kbc_base.smt_valid exC_op 0 0 w'"
  then obtain lf sb where v: "kbc_base.smt_valid (Update 0 Empty (Occupied 1)) 0 0 (lf, sb)"
    unfolding exC_op_def by (metis prod.exhaust)
  then have pok1: "kbc_base.path_ok Empty 0 sb 0"
    and pok2: "kbc_base.path_ok (Occupied 1) 0 sb 0"
    by (simp_all add: kbc_base.smt_valid.simps)
  from pok1[unfolded kbc_base.path_ok_def] have "length sb = 1"
    by (simp add: kb_params_def)
  then obtain s where sb: "sb = [s]"
    by (cases sb) auto
  from pok1 sb have "kb_h_node (kb_h_leaf Empty) s = 0"
    by (simp add: kbc_base.path_ok_def)
  then have e1: "2 * s = 0"
    by (simp add: kb_h_node_def kb_h_leaf_def)
  from pok2 sb have "kb_h_node (kb_h_leaf (Occupied 1)) s = 0"
    by (simp add: kbc_base.path_ok_def)
  then have "4 + 2 * s = 0"
    by (simp add: kb_h_node_def kb_h_leaf_def)
  then have "(4 :: koala_bear) = 0"
    by (simp add: e1)
  then have "(2 :: koala_bear) * 2 = 0"
    by simp
  then have "(2 :: koala_bear) = 0"
    using mult_eq_0_iff [THEN iffD1] by blast
    \<comment> \<open>resolution, not simp: simp folds \<open>2 * 2\<close> into the numeral \<open>4\<close> before
       \<open>mult_eq_0_iff\<close> can see a product, and \<open>4 = 0\<close> alone yields nothing\<close>
  with kb_two_ne_zero show False ..
qed

subsection \<open>Public-input, echo and length premises\<close>

lemma exC_pub: "kbc.pub_ok exC_op 0 0 exC_vd"
  unfolding kbc.pub_ok_def kbc.vd_ok_def
  by (simp add: exC_op_def exC_vd_def kb_params_def)

lemma exC_wlen: "length (snd exC_w) = depth kb_params"
  by (simp add: exC_w_def kb_params_def)

lemma exC_echo: "kbc.echo_ok exC_op exC_w"
  by (simp add: kbc.echo_ok_def exC_op_def exC_w_def)

subsection \<open>Chain shape (the wf premise, discharged by computation)\<close>

lemma exC_descs_up_explicit:
  "kbc_base.descs_up = [RDiff 0 4, RDiff 1 6, RDiff 2 5, RDiff 3 7,
                   RDiff 5 9, RDiff 7 10, RDiff 6 11, RBool 8]"
  by (simp add: kbc_base.descs_up_def upt_rec)

lemma exC_res_gates_in:
  "\<forall>g \<in> set (layer_gates (mk_res_layer (kbc_base.descs (kind_of exC_op)) :: koala_bear layer)).
     g_in1 g < 2 ^ 12 \<and> g_in2 g < 2 ^ 12"
  by (simp add: mk_res_layer_def exC_descs_up_explicit)

lemma exC_q_gates_in:
  "\<forall>g \<in> set (layer_gates (mk_q_layer kb_up_stack_desc :: koala_bear layer)).
     g_in1 g < 2 ^ 13 \<and> g_in2 g < 2 ^ 13"
  by (simp add: mk_q_layer_def kb_up_stack_desc_def qw_gates_def)

context
  fixes exC_enc :: "koala_bear list"
    and exC_bels :: "koala_bear list list"
  defines exC_enc_def: "exC_enc \<equiv> kbc_base.encode_witness exC_op 0 0 exC_vd exC_w"
    and exC_bels_def:
      "exC_bels \<equiv> tl (circuit_values
         (mk_res_layer (kbc_base.descs (kind_of exC_op)) # kb_stack (kind_of exC_op)) exC_enc)"
begin

lemma exC_bels_explicit:
  "exC_bels = [layer_eval (mk_q_layer kb_up_stack_desc) exC_enc, exC_enc]"
  by (simp add: exC_bels_def kb_stack_def Let_def)

lemma exC_wf:
  "gkr_chain_wf [12, 13]
     (mk_res_layer (kbc_base.descs (kind_of exC_op)) # kb_stack (kind_of exC_op)) exC_bels"
proof -
  have stack: "kb_stack (kind_of exC_op) = [mk_q_layer kb_up_stack_desc]"
    by (simp add: kb_stack_def)
  have wb: "layer_width_bits (mk_q_layer kb_up_stack_desc :: koala_bear layer) = 12"
    by (simp add: mk_q_layer_def kb_up_stack_desc_def)
  show ?thesis
    unfolding stack exC_bels_explicit
    using exC_res_gates_in exC_q_gates_in
    by (simp add: stack wb)
qed

section \<open>Theorem C, activated\<close>

text \<open>All premises of the composed soundness theorem are discharged for
  the concrete scenario: the chain-shape premise by computation over the
  actual compiled layers, the representation premise by the mpoly
  interpolation representative with \<open>dbnd = (\<lambda>s. 2 * s)\<close>, the
  public-input/echo/length premises by evaluation, and the semantic
  unsatisfiability by the root-equation argument above.  The bound fact
  binds the composed soundness error
  \<open>(|residuals| + \<Sum>(2 s \<cdot> 2 s + 1)) / |KoalaBear|\<close> for the concrete
  Update against ANY adversary.  (Fact binding: the chain event is a
  locale constant, so the specialised statement lives in the instance's
  terms.)\<close>

lemmas instance_theorem_C_activation =
  kbs.theorem_C_composition[where dbnd = "\<lambda>s. 2 * s",
    OF exC_bels_def[unfolded exC_enc_def, THEN meta_eq_to_obj_eq] exC_wf layer_repr_mpoly
       exC_pub exC_wlen exC_echo exC_nosem]

end

end
