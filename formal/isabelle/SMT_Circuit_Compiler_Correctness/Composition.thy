(*
  Title:   Composition.thy
  Session: SMT_Circuit_Compiler_Correctness (SMT-specific layer)

  Theorem C - composition of Theorem A (deterministic compilation
  soundness) and Theorem B (probabilistic GKR assembly soundness):

    If the facade public-input checks pass and the operation is NOT
    semantically valid between the claimed roots (no witness makes
    smt_valid hold), then the GKR chain bad event for the COMPILED
    circuit with the all-zero claimed output table (the S-4 acceptance
    convention) has probability at most

      (|residual layer| + sum over layers of (2 s_i dbnd + 1)) / |'a|

    over the verifier randomness, for ANY adversary.

  Composition pattern: CDSP Theorem 3 (assume-guarantee).  Theorem A
  contributes the deterministic step: semantic invalidity propagates
  (via the contrapositive of theorem_A_soundness) to NON-acceptance of
  the compiled circuit on the honest witness encoding, i.e. the TRUE
  output table is nonzero somewhere.  Theorem B contributes the
  probabilistic step: a claimed output table that differs from the true
  one survives the layer-reduction chain only with the stated
  probability (gkr_assembly_soundness).

  No knowledge claim is made (property boundary): the conclusion bounds
  the probability of the chain event, it does not extract a witness.

  Model boundary notes:
  - The chain-shape premise (gkr_chain_wf) packages the structural facts
    of the compiled circuit's layer list - gate fan-in ranges and layer
    widths of the evaluation stack.  The stack is an ABSTRACT locale
    parameter, so these facts are dischargeable only
    at instantiation with a concrete stack; they are refinement-adjacent
    obligations, not semantic assumptions.
  - The bridge to the concrete verifier (real verifier acceptance implies
    the model chain event) is documented at gkr_chain_bad (GKR_Assembly).
*)

theory Composition
  imports Compiler_Correctness GKR_Protocol.GKR_Assembly
begin

section \<open>The composition locale (v0.1 pipeline)\<close>

text \<open>
  The compiler model and the GKR bridge locale over ONE challenge field:
  the compiler's wire field is the (finite) field the sumcheck
  challenges are drawn from.  (Production splits base and challenge
  fields; the model identifies them - the extension-field split is an
  optimisation seam, not a semantic one.)
\<close>

locale statesync_gkr_v01 =
  compiler_model params h_leaf h_node W L digest_repr leaf_repr hl hn stack +
  gkr_layer_sumcheck vars deg eval inst
  for params :: smt_params
    and h_leaf :: "'v leaf_state \<Rightarrow> 'd"
    and h_node :: "'d \<Rightarrow> 'd \<Rightarrow> 'd"
    and W L :: nat
    and digest_repr :: "'d \<Rightarrow> 'a::{finite, field} list"
    and leaf_repr :: "'v leaf_state \<Rightarrow> 'a list"
    and hl :: "'a list \<Rightarrow> 'a list"
    and hn :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
    and stack :: "op_kind \<Rightarrow> 'a layer list"
    and vars :: "'p::comm_monoid_add \<Rightarrow> nat set"
    and deg :: "'p \<Rightarrow> nat"
    and eval :: "'p \<Rightarrow> (nat, 'a) subst \<Rightarrow> 'a"
    and inst :: "'p \<Rightarrow> (nat, 'a) subst \<Rightarrow> 'p"
begin

text \<open>The compiled circuit's layer list and its value chain on the
  honest witness encoding.\<close>

lemma compile_layers:
  "circ_layers (compile k) = mk_res_layer (descs k) # stack k"
  by (simp add: compile_def)

lemma compile_output_width:
  "layer_width_bits (mk_res_layer (descs k)) = length (descs k)"
  by (simp add: mk_res_layer_def)

section \<open>Theorem C\<close>

theorem theorem_C_composition:
  fixes P :: "'a layer \<Rightarrow> nat \<Rightarrow> ('a list \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'p"
    and A :: "nat \<Rightarrow> 'a list \<Rightarrow> ('p, 'a, 'a, nat, 's) prover \<times> 's \<times> 'a \<times> 'a \<times> 'a"
    and w :: "'v leaf_state \<times> 'd list"
    and root root' vd :: 'd
      \<comment> \<open>explicit: the import chain brings HOL-Analysis' \<open>root\<close> constant
         into scope, which would otherwise capture the variable\<close>
    and dbnd :: "nat \<Rightarrow> nat"
      \<comment> \<open>width-dependent representative degree bound: dischargeable
         with \<open>\<lambda>s. 2 * s\<close> in the AFP total-degree mpoly instance\<close>
  assumes bels: "bels = tl (circuit_values (mk_res_layer (descs (kind_of op)) # stack (kind_of op))
                             (encode_witness op root root' vd w))"
    and wf: "gkr_chain_wf (s0 # ss) (mk_res_layer (descs (kind_of op)) # stack (kind_of op)) bels"
    and repr: "\<And>Ly s claims b. layer_poly_repr (P Ly s claims b) Ly s claims b (dbnd s)"
    and pub: "pub_ok op root root' vd"
    and wlen: "length (snd w) = depth params"
    and echo: "echo_ok op w"
    and nosem: "\<not> (\<exists>w'. smt_valid op root root' w')"
  shows "measure_pmf.prob
           (pmf_of_set (tuples (UNIV :: 'a set)
              (length (descs (kind_of op)) + chain_rlen (s0 # ss))))
           {rs. gkr_chain_bad P (\<lambda>j pfx. A j (take (length (descs (kind_of op))) rs @ pfx))
                  (s0 # ss) (mk_res_layer (descs (kind_of op)) # stack (kind_of op)) bels
                  [(take (length (descs (kind_of op))) rs, 1)]
                  (mle (length (descs (kind_of op))) (\<lambda>_. 0)
                     (take (length (descs (kind_of op))) rs)
                   - const_mle (mk_res_layer (descs (kind_of op)))
                       (take (length (descs (kind_of op))) rs))
                  (drop (length (descs (kind_of op))) rs)}
       \<le> (real (length (descs (kind_of op)))
           + (\<Sum>s\<leftarrow>s0 # ss. real (2 * s) * real (dbnd s) + 1)) / real CARD('a)"
proof -
  let ?k = "kind_of op"
  let ?L0 = "mk_res_layer (descs ?k) :: 'a layer"
    \<comment> \<open>type pinned: \<open>layer_width_bits ?L0\<close> occurrences do not determine
       the layer's wire field, so an unannotated abbreviation would give
       each standalone occurrence a fresh type variable (the type-binding
       pathology this corpus guards against)\<close>
  let ?enc = "encode_witness op root root' vd w"
  let ?cvs = "circuit_values (?L0 # stack ?k) ?enc"

  \<comment> \<open>Theorem A, contrapositive: semantic invalidity kills circuit acceptance\<close>
  have not_accept: "\<not> circuit_accept (compile ?k) ?enc"
  proof
    assume "circuit_accept (compile ?k) ?enc"
    then have "verifier_accept op root root' vd w"
      using pub wlen echo by (simp add: verifier_accept_def)
    then have "smt_valid op root root' (canon_witness op w)"
      by (rule theorem_A_soundness)
    with nosem show False by blast
  qed

  \<comment> \<open>the below vector of the residual layer, and the true output table\<close>
  obtain b0 bs where bels_cons: "bels = b0 # bs"
    using wf by (cases bels) auto
  have tl_cvs: "tl ?cvs = circuit_values (stack ?k) ?enc"
    by (simp add: Let_def)
  have hd_cvs: "hd ?cvs = layer_eval ?L0 (hd (circuit_values (stack ?k) ?enc))"
    by (simp add: Let_def)
  have b0_hd: "b0 = hd (circuit_values (stack ?k) ?enc)"
  proof -
    have "b0 # bs = bels" by (rule bels_cons[symmetric])
    also have "\<dots> = tl ?cvs" by (rule bels)
    also have "\<dots> = circuit_values (stack ?k) ?enc" by (rule tl_cvs)
    finally have "hd (b0 # bs) = hd (circuit_values (stack ?k) ?enc)"
      by (rule arg_cong)
    then show ?thesis by simp
  qed
  have out_eq: "circuit_output (compile ?k) ?enc = layer_eval ?L0 b0"
  proof -
    have "circuit_output (compile ?k) ?enc = hd ?cvs"
      unfolding circuit_output_def compile_layers by (rule refl)
    also have "\<dots> = layer_eval ?L0 (hd (circuit_values (stack ?k) ?enc))"
      by (rule hd_cvs)
    also have "\<dots> = layer_eval ?L0 b0"
      by (simp add: b0_hd[symmetric])
    finally show ?thesis .
  qed

  \<comment> \<open>the all-zero claimed table differs from the true output somewhere\<close>
  have outs_ne: "\<exists>idx < 2 ^ layer_width_bits ?L0. (\<lambda>_. 0 :: 'a) idx \<noteq> layer_eval ?L0 b0 ! idx"
  proof -
    from not_accept obtain x where x_in: "x \<in> set (circuit_output (compile ?k) ?enc)"
      and x_ne: "x \<noteq> 0"
      by (auto simp add: circuit_accept_def)
    from x_in obtain idx where idx_lt: "idx < length (circuit_output (compile ?k) ?enc)"
      and idx_eq: "circuit_output (compile ?k) ?enc ! idx = x"
      by (auto simp add: in_set_conv_nth)
    have "length (circuit_output (compile ?k) ?enc) = 2 ^ layer_width_bits ?L0"
      by (simp add: out_eq layer_width_def)
    then show ?thesis
      using idx_lt idx_eq x_ne by (auto simp add: out_eq)
  qed

  have "measure_pmf.prob
          (pmf_of_set (tuples (UNIV :: 'a set)
             (layer_width_bits ?L0 + chain_rlen (s0 # ss))))
          {rs. gkr_chain_bad P (\<lambda>j pfx. A j (take (layer_width_bits ?L0) rs @ pfx))
                 (s0 # ss) (?L0 # stack ?k) (b0 # bs)
                 [(take (layer_width_bits ?L0) rs, 1)]
                 (mle (layer_width_bits ?L0) (\<lambda>_. 0) (take (layer_width_bits ?L0) rs)
                  - const_mle ?L0 (take (layer_width_bits ?L0) rs))
                 (drop (layer_width_bits ?L0) rs)}
      \<le> (real (layer_width_bits ?L0)
          + (\<Sum>s\<leftarrow>s0 # ss. real (2 * s) * real (dbnd s) + 1)) / real CARD('a)"
    using wf bels_cons
    by (intro gkr_assembly_soundness[OF _ repr outs_ne]) simp
  then show ?thesis
    by (simp add: bels_cons compile_output_width)
qed

text \<open>
  The design-bound specialisation (reduce.rs \<open>LAYER_ROUND_DEGREE\<close> = 4):
  the composed pipeline's soundness error is
  \<open>(|residuals| + sum over layers of (8 s_i + 1)) / |'a|\<close>.
\<close>

corollary theorem_C_composition_deg4:
  fixes P :: "'a layer \<Rightarrow> nat \<Rightarrow> ('a list \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'p"
    and A :: "nat \<Rightarrow> 'a list \<Rightarrow> ('p, 'a, 'a, nat, 's) prover \<times> 's \<times> 'a \<times> 'a \<times> 'a"
    and w :: "'v leaf_state \<times> 'd list"
    and root root' vd :: 'd
  assumes "bels = tl (circuit_values (mk_res_layer (descs (kind_of op)) # stack (kind_of op))
                       (encode_witness op root root' vd w))"
    and "gkr_chain_wf (s0 # ss) (mk_res_layer (descs (kind_of op)) # stack (kind_of op)) bels"
    and "\<And>Ly s claims b. layer_poly_repr (P Ly s claims b) Ly s claims b 4"
    and "pub_ok op root root' vd"
    and "length (snd w) = depth params"
    and "echo_ok op w"
    and "\<not> (\<exists>w'. smt_valid op root root' w')"
  shows "measure_pmf.prob
           (pmf_of_set (tuples (UNIV :: 'a set)
              (length (descs (kind_of op)) + chain_rlen (s0 # ss))))
           {rs. gkr_chain_bad P (\<lambda>j pfx. A j (take (length (descs (kind_of op))) rs @ pfx))
                  (s0 # ss) (mk_res_layer (descs (kind_of op)) # stack (kind_of op)) bels
                  [(take (length (descs (kind_of op))) rs, 1)]
                  (mle (length (descs (kind_of op))) (\<lambda>_. 0)
                     (take (length (descs (kind_of op))) rs)
                   - const_mle (mk_res_layer (descs (kind_of op)))
                       (take (length (descs (kind_of op))) rs))
                  (drop (length (descs (kind_of op))) rs)}
       \<le> (real (length (descs (kind_of op)))
           + (\<Sum>s\<leftarrow>s0 # ss. real (2 * s) * 4 + 1)) / real CARD('a)"
proof -
  have r: "\<And>Ly s claims b. layer_poly_repr (P Ly s claims b) Ly s claims b ((\<lambda>_. 4) s)"
    using assms(3) by simp
  show ?thesis
    using theorem_C_composition[OF assms(1,2) r assms(4-7)] by simp
qed

end

end
