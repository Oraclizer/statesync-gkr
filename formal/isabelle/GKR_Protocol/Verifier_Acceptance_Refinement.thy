(*
  Title:   Verifier_Acceptance_Refinement.thy
  Session: GKR_Protocol

  Forward refinement boundary from the production Rust verifier's successful
  return to GKR_Assembly.gkr_chain_bad.  This theory does not model Rust,
  Fiat-Shamir, or foreign-field arithmetic.  It mechanises the existing
  GKR_Assembly MODEL BOUNDARY: once the concrete round checks and wiring/carry
  reconstruction are related to the true layer polynomial, the final input
  MLE checks make every accepting execution inhabit gkr_chain_bad.

  NAMING.  "production" names the shipped Rust verifier body, as opposed to
  the abstract model, and matches the wording of the Rust source this theory
  refines.  It is not a maturity claim: the repository states that this is
  unaudited research software and not production software, and nothing here
  changes that.

  SCOPE.  The final corollary is conditional.  It carries
  rust_hol_value_trace_relation as an explicit, deliberately load-bearing
  premise, which is not discharged against the compiled Rust program.  No
  axiom is added and the reverse implication is stated as a non-claim.
*)

theory Verifier_Acceptance_Refinement
  imports GKR_Assembly
begin

section \<open>The production acceptance gate\<close>

record acceptance_trace =
  public_inputs_bound :: bool
  request_guards_bound :: bool
  zero_output_claim :: bool
  sumcheck_consistent :: bool
  carry_consistent :: bool
  final_mle_x :: bool
  final_mle_y :: bool

record chain_acceptance_trace =
  chain_sumcheck_consistent :: bool
  chain_carry_consistent :: bool
  chain_final_mle_x :: bool
  chain_final_mle_y :: bool

definition executable_accepts :: "acceptance_trace \<Rightarrow> bool" where
  "executable_accepts t \<longleftrightarrow>
     public_inputs_bound t \<and>
     request_guards_bound t \<and>
     zero_output_claim t \<and>
     sumcheck_consistent t \<and>
     carry_consistent t \<and>
     final_mle_x t \<and>
     final_mle_y t"

definition honest_acceptance_trace :: acceptance_trace where
  "honest_acceptance_trace =
     \<lparr> public_inputs_bound = True,
       request_guards_bound = True,
       zero_output_claim = True,
       sumcheck_consistent = True,
       carry_consistent = True,
       final_mle_x = True,
       final_mle_y = True \<rparr>"

lemma executable_accepts_positive_witness:
  "executable_accepts honest_acceptance_trace"
  by (simp add: executable_accepts_def honest_acceptance_trace_def)

lemma public_input_mutation_rejected:
  "\<not> executable_accepts (honest_acceptance_trace\<lparr>public_inputs_bound := False\<rparr>)"
  by (simp add: executable_accepts_def honest_acceptance_trace_def)

lemma sumcheck_mutation_rejected:
  "\<not> executable_accepts (honest_acceptance_trace\<lparr>sumcheck_consistent := False\<rparr>)"
  by (simp add: executable_accepts_def honest_acceptance_trace_def)

lemma carry_mutation_rejected:
  "\<not> executable_accepts (honest_acceptance_trace\<lparr>carry_consistent := False\<rparr>)"
  by (simp add: executable_accepts_def honest_acceptance_trace_def)

lemma final_mle_x_mutation_rejected:
  "\<not> executable_accepts (honest_acceptance_trace\<lparr>final_mle_x := False\<rparr>)"
  by (simp add: executable_accepts_def honest_acceptance_trace_def)

lemma final_mle_y_mutation_rejected:
  "\<not> executable_accepts (honest_acceptance_trace\<lparr>final_mle_y := False\<rparr>)"
  by (simp add: executable_accepts_def honest_acceptance_trace_def)

section \<open>Layer-chain refinement\<close>

type_synonym ('p, 'a, 's) verifier_adversary =
  "nat \<Rightarrow> 'a list \<Rightarrow> ('p, 'a, 'a, nat, 's) prover \<times> 's \<times> 'a \<times> 'a \<times> 'a"

type_synonym ('p, 'a, 's) verifier_local_check =
  "('p, 'a, 's) verifier_adversary \<Rightarrow>
   nat list \<Rightarrow> 'a layer list \<Rightarrow> 'a list list \<Rightarrow>
   ('a list \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool"

type_synonym ('p, 'a, 's) verifier_finish_check =
  "('p, 'a, 's) verifier_adversary \<Rightarrow>
   nat list \<Rightarrow> 'a layer list \<Rightarrow> 'a list list \<Rightarrow>
   ('a list \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow>
   'p \<Rightarrow> 'a \<Rightarrow> bool"

type_synonym ('p, 'a, 's) verifier_finish_value =
  "('p, 'a, 's) verifier_adversary \<Rightarrow>
   nat list \<Rightarrow> 'a layer list \<Rightarrow> 'a list list \<Rightarrow>
   ('a list \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a"

context gkr_layer_sumcheck
begin

fun verifier_sumcheck_trace ::
  "('p \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('p, 'a, 'a, nat, 's) prover \<Rightarrow> 's \<Rightarrow>
   ('p, 'a, 'a) sc_inst \<Rightarrow> 'a \<Rightarrow> (nat \<times> 'a) list \<Rightarrow> bool" where
  "verifier_sumcheck_trace finish pr ps (H, p, v) r_prev [] \<longleftrightarrow>
     finish p v"
| "verifier_sumcheck_trace finish pr ps (H, p, v) r_prev ((x, r) # rm) \<longleftrightarrow>
     (let (q, ps') = pr (H, p, v) x (map fst rm) r_prev ps in
        vars q \<subseteq> {x} \<and> deg q \<le> deg p \<and>
        v = (\<Sum>y \<in> H. eval q [x \<mapsto> y]) \<and>
        verifier_sumcheck_trace finish pr ps'
          (H, inst p [x \<mapsto> r], eval q [x \<mapsto> r]) r rm)"

lemma verifier_sumcheck_trace_refines_sumcheck:
  assumes finish_refines: "\<And>p v. finish p v \<Longrightarrow> v = eval p Map.empty"
    and traced: "verifier_sumcheck_trace finish pr ps (H, p, v) r_prev rm"
  shows "sumcheck pr ps (H, p, v) r_prev rm"
  using traced
proof (induction rm arbitrary: p v ps r_prev)
  case Nil
  then show ?case using finish_refines by simp
next
  case (Cons xr rm)
  obtain x r where xr: "xr = (x, r)" by (cases xr)
  obtain q ps' where step: "pr (H, p, v) x (map fst rm) r_prev ps = (q, ps')"
    by fastforce
  from Cons.prems have vars: "vars q \<subseteq> {x}" and degree: "deg q \<le> deg p"
    and sum: "v = (\<Sum>y \<in> H. eval q [x \<mapsto> y])"
    and tail: "verifier_sumcheck_trace finish pr ps'
      (H, inst p [x \<mapsto> r], eval q [x \<mapsto> r]) r rm"
    by (simp_all add: xr step)
  have "sumcheck pr ps' (H, inst p [x \<mapsto> r], eval q [x \<mapsto> r]) r rm"
    using Cons.IH[OF tail] .
  then show ?case
    by (simp add: xr step vars degree sum[symmetric])
qed

definition true_carry ::
  "('p, 'a, 's) verifier_adversary \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "true_carry A s b rs \<longleftrightarrow>
     (case A 0 (take (2 * s) rs) of (pr, ps, r0, tx, ty) \<Rightarrow>
        tx = mle s ((!) b) (take s rs) \<and>
        ty = mle s ((!) b) (take s (drop s rs)))"

fun concrete_finish_check ::
  "('p, 'a, 's) verifier_finish_value \<Rightarrow>
   ('p, 'a, 's) verifier_finish_value \<Rightarrow>
   ('p, 'a, 's) verifier_finish_check" where
  "concrete_finish_check final_claim wiring_rhs
      A (s # ss) (L # Ls) (b # bs) claims v rs p final_v \<longleftrightarrow>
     (final_v = final_claim A (s # ss) (L # Ls) (b # bs) claims v rs \<and>
      final_claim A (s # ss) (L # Ls) (b # bs) claims v rs
        = wiring_rhs A (s # ss) (L # Ls) (b # bs) claims v rs \<and>
      (true_carry A s b rs \<longrightarrow>
        wiring_rhs A (s # ss) (L # Ls) (b # bs) claims v rs
          = eval p Map.empty))"
| "concrete_finish_check final_claim wiring_rhs
      A ss Ls bs claims v rs p final_v \<longleftrightarrow> False"

definition true_polynomial_sumcheck ::
  "('a layer \<Rightarrow> nat \<Rightarrow> ('a list \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'p) \<Rightarrow>
   ('p, 'a, 's) verifier_adversary \<Rightarrow>
   nat \<Rightarrow> 'a layer \<Rightarrow> 'a list \<Rightarrow>
   ('a list \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "true_polynomial_sumcheck P A s L b claims v rs \<longleftrightarrow>
     (case A 0 [] of (pr, ps, r0, tx, ty) \<Rightarrow>
        sumcheck pr ps ({0, 1}, P L s claims b, v) r0
          (zip (upt 0 (2 * s)) (take (2 * s) rs)))"

fun concrete_round_check ::
  "('a layer \<Rightarrow> nat \<Rightarrow> ('a list \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'p) \<Rightarrow>
   ('p, 'a, 's) verifier_finish_check \<Rightarrow>
   ('p, 'a, 's) verifier_local_check" where
  "concrete_round_check P finish_ok A (s # ss) (L # Ls) (b # bs) claims v rs \<longleftrightarrow>
     (case A 0 [] of (pr, ps, r0, tx, ty) \<Rightarrow>
        verifier_sumcheck_trace
          (finish_ok A (s # ss) (L # Ls) (b # bs) claims v rs)
          pr ps ({0, 1}, P L s claims b, v) r0
          (zip (upt 0 (2 * s)) (take (2 * s) rs)))"
| "concrete_round_check P finish_ok A ss Ls bs claims v rs \<longleftrightarrow> False"

fun concrete_finish_relation ::
  "('p, 'a, 's) verifier_finish_check \<Rightarrow>
   ('p, 'a, 's) verifier_local_check" where
  "concrete_finish_relation finish_ok A (s # ss) (L # Ls) (b # bs) claims v rs \<longleftrightarrow>
     (true_carry A s b rs \<longrightarrow>
       (\<forall>p v'. finish_ok A (s # ss) (L # Ls) (b # bs) claims v rs p v'
          \<longrightarrow> v' = eval p Map.empty))"
| "concrete_finish_relation finish_ok A ss Ls bs claims v rs \<longleftrightarrow> False"

lemma concrete_finish_check_supplies_relation:
  "concrete_finish_relation (concrete_finish_check final_claim wiring_rhs)
     A (s # ss) (L # Ls) (b # bs) claims v rs"
  by auto

lemma concrete_checks_supply_local_bridge:
  assumes wf: "gkr_chain_wf (s # ss) (L # Ls) (b # bs)"
    and rounds:
      "concrete_round_check P finish_ok A (s # ss) (L # Ls) (b # bs) claims v rs"
    and finish:
      "concrete_finish_relation finish_ok A (s # ss) (L # Ls) (b # bs) claims v rs"
    and carry: "true_carry A s b rs"
  shows "true_polynomial_sumcheck P A s L b claims v rs"
proof -
  obtain pr ps r0 tx ty where adv0: "A 0 [] = (pr, ps, r0, tx, ty)"
    using prod_cases5 by blast
  have traced: "verifier_sumcheck_trace
      (finish_ok A (s # ss) (L # Ls) (b # bs) claims v rs)
      pr ps ({0, 1}, P L s claims b, v) r0
      (zip (upt 0 (2 * s)) (take (2 * s) rs))"
    using rounds by (simp add: adv0)
  have finish_refines:
      "\<And>p v'. finish_ok A (s # ss) (L # Ls) (b # bs) claims v rs p v'
        \<Longrightarrow> v' = eval p Map.empty"
    using finish carry by simp
  have "sumcheck pr ps ({0, 1}, P L s claims b, v) r0
      (zip (upt 0 (2 * s)) (take (2 * s) rs))"
    by (rule verifier_sumcheck_trace_refines_sumcheck[OF finish_refines traced])
  then show ?thesis
    by (simp add: true_polynomial_sumcheck_def adv0)
qed

fun verifier_chain_accepts ::
  "('p, 'a, 's) verifier_local_check \<Rightarrow>
   ('p, 'a, 's) verifier_local_check \<Rightarrow>
   ('p, 'a, 's) verifier_adversary \<Rightarrow>
   nat list \<Rightarrow> 'a layer list \<Rightarrow> 'a list list \<Rightarrow>
   ('a list \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "verifier_chain_accepts round_ok carry_ok A (s # ss) (L # Ls) (b # bs) claims v rs =
     (round_ok A (s # ss) (L # Ls) (b # bs) claims v rs \<and>
      carry_ok A (s # ss) (L # Ls) (b # bs) claims v rs \<and>
      (case A 0 (take (2 * s) rs) of (pr, ps, r0, tx, ty) \<Rightarrow>
         if Ls = [] then
           tx = mle s ((!) b) (take s rs) \<and>
           ty = mle s ((!) b) (take s (drop s rs))
         else
           verifier_chain_accepts round_ok carry_ok
             (\<lambda>j pfx. A (Suc j) (take (2 * s + 1) rs @ pfx))
             ss Ls bs
             [(take s rs, 1), (take s (drop s rs), rs ! (2 * s))]
             ((tx - const_mle (hd Ls) (take s rs))
                + rs ! (2 * s) *
                    (ty - const_mle (hd Ls) (take s (drop s rs))))
             (drop (2 * s + 1) rs)))"
| "verifier_chain_accepts round_ok carry_ok A ss Ls bs claims v rs = False"

fun verifier_chain_trace ::
  "('p, 'a, 's) verifier_local_check \<Rightarrow>
   ('p, 'a, 's) verifier_local_check \<Rightarrow>
   ('p, 'a, 's) verifier_adversary \<Rightarrow>
   nat list \<Rightarrow> 'a layer list \<Rightarrow> 'a list list \<Rightarrow>
   ('a list \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow>
   chain_acceptance_trace" where
  "verifier_chain_trace round_ok carry_ok A (s # ss) (L # Ls) (b # bs) claims v rs =
     (case A 0 (take (2 * s) rs) of (pr, ps, r0, tx, ty) \<Rightarrow>
        if Ls = [] then
          \<lparr> chain_sumcheck_consistent =
               round_ok A (s # ss) (L # Ls) (b # bs) claims v rs,
             chain_carry_consistent =
               carry_ok A (s # ss) (L # Ls) (b # bs) claims v rs,
             chain_final_mle_x = tx = mle s ((!) b) (take s rs),
             chain_final_mle_y = ty = mle s ((!) b) (take s (drop s rs)) \<rparr>
        else
          (let tail = verifier_chain_trace round_ok carry_ok
             (\<lambda>j pfx. A (Suc j) (take (2 * s + 1) rs @ pfx))
             ss Ls bs
             [(take s rs, 1), (take s (drop s rs), rs ! (2 * s))]
             ((tx - const_mle (hd Ls) (take s rs))
               + rs ! (2 * s) *
                   (ty - const_mle (hd Ls) (take s (drop s rs))))
             (drop (2 * s + 1) rs)
           in \<lparr> chain_sumcheck_consistent =
                 round_ok A (s # ss) (L # Ls) (b # bs) claims v rs
                   \<and> chain_sumcheck_consistent tail,
               chain_carry_consistent =
                 carry_ok A (s # ss) (L # Ls) (b # bs) claims v rs
                   \<and> chain_carry_consistent tail,
               chain_final_mle_x = chain_final_mle_x tail,
               chain_final_mle_y = chain_final_mle_y tail \<rparr>))"
| "verifier_chain_trace round_ok carry_ok A ss Ls bs claims v rs =
     \<lparr> chain_sumcheck_consistent = False,
       chain_carry_consistent = False,
       chain_final_mle_x = False,
       chain_final_mle_y = False \<rparr>"

lemma verifier_chain_accepts_iff_trace:
  assumes wf: "gkr_chain_wf ss Ls bels"
  shows "verifier_chain_accepts round_ok carry_ok A ss Ls bels claims v rs \<longleftrightarrow>
     (let t = verifier_chain_trace round_ok carry_ok A ss Ls bels claims v rs in
        chain_sumcheck_consistent t \<and> chain_carry_consistent t \<and>
        chain_final_mle_x t \<and> chain_final_mle_y t)"
  using wf
proof (induction ss Ls bels arbitrary: A claims v rs rule: gkr_chain_wf.induct)
  case (1 A claims v rs)
  then show ?case by simp
next
  case (2 s L b A claims v rs)
  then show ?case
    by (auto simp add: Let_def split: prod.splits)
next
  case (3 s s' ss L L' Ls b b' bs A claims v rs)
  let ?seg = "take (2 * s) rs"
  obtain pr ps r0 tx ty where adv:
      "A 0 ?seg = (pr, ps, r0, tx, ty)"
    using prod_cases5 by blast
  let ?A' =
    "\<lambda>j pfx. A (Suc j) (take (2 * s + 1) rs @ pfx)"
  let ?claims' =
    "[(take s rs, 1), (take s (drop s rs), rs ! (2 * s))]"
  let ?v' =
    "(tx - const_mle L' (take s rs))
      + rs ! (2 * s) * (ty - const_mle L' (take s (drop s rs)))"
  let ?rs' = "drop (2 * s + 1) rs"
  have wf_tail:
      "gkr_chain_wf (s' # ss) (L' # Ls) (b' # bs)"
    using "3.prems" by simp
  have tail_iff:
      "verifier_chain_accepts round_ok carry_ok ?A'
         (s' # ss) (L' # Ls) (b' # bs) ?claims' ?v' ?rs'
       \<longleftrightarrow>
       (let t = verifier_chain_trace round_ok carry_ok ?A'
          (s' # ss) (L' # Ls) (b' # bs) ?claims' ?v' ?rs'
        in chain_sumcheck_consistent t \<and>
           chain_carry_consistent t \<and>
           chain_final_mle_x t \<and>
           chain_final_mle_y t)"
    using "3.IH"[OF wf_tail] .
  show ?case
    apply (subst verifier_chain_accepts.simps(1))
    apply (subst verifier_chain_trace.simps(1))
    using tail_iff
    by (auto simp add: adv Let_def
             del: verifier_chain_accepts.simps verifier_chain_trace.simps
             split: prod.splits)
qed simp_all

definition production_verifier_accepts :: "acceptance_trace \<Rightarrow> bool" where
  "production_verifier_accepts t \<longleftrightarrow> executable_accepts t"

definition concrete_trace_relation ::
  "acceptance_trace \<Rightarrow>
   ('p, 'a, 's) verifier_local_check \<Rightarrow>
   ('p, 'a, 's) verifier_local_check \<Rightarrow>
   ('p, 'a, 's) verifier_adversary \<Rightarrow>
   nat list \<Rightarrow> 'a layer list \<Rightarrow> 'a list list \<Rightarrow>
   ('a list \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "concrete_trace_relation t round_ok carry_ok A ss Ls bels claims v rs \<longleftrightarrow>
     (let model = verifier_chain_trace round_ok carry_ok A ss Ls bels claims v rs in
        sumcheck_consistent t = chain_sumcheck_consistent model \<and>
        carry_consistent t = chain_carry_consistent model \<and>
        final_mle_x t = chain_final_mle_x model \<and>
        final_mle_y t = chain_final_mle_y model)"

definition rust_hol_trace_relation ::
  "acceptance_trace \<Rightarrow>
   ('a layer \<Rightarrow> nat \<Rightarrow> ('a list \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'p) \<Rightarrow>
   ('p, 'a, 's) verifier_finish_check \<Rightarrow>
   ('p, 'a, 's) verifier_adversary \<Rightarrow>
   nat list \<Rightarrow> 'a layer list \<Rightarrow> 'a list list \<Rightarrow>
   ('a list \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "rust_hol_trace_relation t P finish_ok A ss Ls bels claims v rs \<longleftrightarrow>
     concrete_trace_relation t
       (concrete_round_check P finish_ok)
       (concrete_finish_relation finish_ok)
       A ss Ls bels claims v rs"

definition rust_hol_value_trace_relation ::
  "acceptance_trace \<Rightarrow>
   ('a layer \<Rightarrow> nat \<Rightarrow> ('a list \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'p) \<Rightarrow>
   ('p, 'a, 's) verifier_finish_value \<Rightarrow>
   ('p, 'a, 's) verifier_finish_value \<Rightarrow>
   ('p, 'a, 's) verifier_adversary \<Rightarrow>
   nat list \<Rightarrow> 'a layer list \<Rightarrow> 'a list list \<Rightarrow>
   ('a list \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "rust_hol_value_trace_relation t P final_claim wiring_rhs
      A ss Ls bels claims v rs \<longleftrightarrow>
     rust_hol_trace_relation t P
       (concrete_finish_check final_claim wiring_rhs)
       A ss Ls bels claims v rs"

text \<open>
  The sole semantic premise below is the already documented concrete-to-model
  boundary in GKR_Assembly: if the actual round checks and the actual wiring
  reconstruction both pass and the carried evaluations are true, those same
  messages constitute AFP acceptance for the true representative polynomial.
  False carries need no premise; the recursion records them, and the final
  input MLE checks rule them out at the last layer.
\<close>

theorem verifier_acceptance_implies_gkr_chain_bad:
  fixes P :: "'a layer \<Rightarrow> nat \<Rightarrow> ('a list \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'p"
    and A :: "('p, 'a, 's) verifier_adversary"
    and round_ok carry_ok :: "('p, 'a, 's) verifier_local_check"
  assumes wf: "gkr_chain_wf ss Ls bels"
    and local_bridge:
      "\<And>A s ss L Ls b bs claims v rs.
         gkr_chain_wf (s # ss) (L # Ls) (b # bs) \<Longrightarrow>
         round_ok A (s # ss) (L # Ls) (b # bs) claims v rs \<Longrightarrow>
         carry_ok A (s # ss) (L # Ls) (b # bs) claims v rs \<Longrightarrow>
         true_carry A s b rs \<Longrightarrow>
         true_polynomial_sumcheck P A s L b claims v rs"
    and accepted: "verifier_chain_accepts round_ok carry_ok A ss Ls bels claims v rs"
  shows "gkr_chain_bad P A ss Ls bels claims v rs"
  using wf accepted
proof (induction ss Ls bels arbitrary: A claims v rs rule: gkr_chain_wf.induct)
  case (1 A claims v rs)
  then show ?case by simp
next
  case (2 s L b A claims v rs)
  then have rounds:
      "round_ok A [s] [L] [b] claims v rs"
    and carry: "carry_ok A [s] [L] [b] claims v rs"
    and tc: "true_carry A s b rs"
    by (auto simp add: true_carry_def split: prod.splits if_splits)
  from local_bridge[OF "2.prems"(1) rounds carry tc]
  show ?case
    by (simp add: true_polynomial_sumcheck_def gkr_chain_bad.simps split: prod.splits)
next
  case (3 s s' ss L L' Ls b b' bs A claims v rs)
  let ?seg = "take (2 * s) rs"
  obtain pr ps r0 tx ty where adv: "A 0 ?seg = (pr, ps, r0, tx, ty)"
    using prod_cases5 by blast
  have wf_tail: "gkr_chain_wf (s' # ss) (L' # Ls) (b' # bs)"
    using "3.prems"(1) by simp
  from "3.prems"(2) have rounds:
      "round_ok A (s # s' # ss) (L # L' # Ls) (b # b' # bs) claims v rs"
    and carry: "carry_ok A (s # s' # ss) (L # L' # Ls) (b # b' # bs) claims v rs"
    and tail:
      "verifier_chain_accepts round_ok carry_ok
        (\<lambda>j pfx. A (Suc j) (take (2 * s + 1) rs @ pfx))
        (s' # ss) (L' # Ls) (b' # bs)
        [(take s rs, 1), (take s (drop s rs), rs ! (2 * s))]
        ((tx - const_mle L' (take s rs))
          + rs ! (2 * s) * (ty - const_mle L' (take s (drop s rs))))
        (drop (2 * s + 1) rs)"
    by (simp_all add: adv)
  show ?case
  proof (cases "tx = mle s ((!) b) (take s rs) \<and>
                ty = mle s ((!) b) (take s (drop s rs))")
    case True
    then have tc: "true_carry A s b rs"
      by (simp add: true_carry_def adv)
    have "true_polynomial_sumcheck P A s L b claims v rs"
      using local_bridge[OF "3.prems"(1) rounds carry tc] .
    then show ?thesis
      by (simp add: true_polynomial_sumcheck_def gkr_chain_bad.simps split: prod.splits)
  next
    case False
    have bad_tail:
      "gkr_chain_bad P
        (\<lambda>j pfx. A (Suc j) (take (2 * s + 1) rs @ pfx))
        (s' # ss) (L' # Ls) (b' # bs)
        [(take s rs, 1), (take s (drop s rs), rs ! (2 * s))]
        ((tx - const_mle L' (take s rs))
          + rs ! (2 * s) * (ty - const_mle L' (take s (drop s rs))))
        (drop (2 * s + 1) rs)"
      using "3.IH"[OF wf_tail tail] .
    show ?thesis
      using False bad_tail
      by (simp add: gkr_chain_bad.simps adv)
  qed
qed simp_all

corollary production_verifier_acceptance_refines_gkr_chain_bad:
  fixes P :: "'a layer \<Rightarrow> nat \<Rightarrow> ('a list \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'p"
    and A :: "('p, 'a, 's) verifier_adversary"
    and final_claim wiring_rhs :: "('p, 'a, 's) verifier_finish_value"
  assumes wf: "gkr_chain_wf ss Ls bels"
    and accepted:
      "production_verifier_accepts t"
    and related:
      "rust_hol_value_trace_relation t P final_claim wiring_rhs
        A ss Ls bels claims v rs"
  shows "gkr_chain_bad P A ss Ls bels claims v rs"
proof -
  from accepted related have observed:
    "(let model = verifier_chain_trace
        (concrete_round_check P (concrete_finish_check final_claim wiring_rhs))
        (concrete_finish_relation (concrete_finish_check final_claim wiring_rhs))
        A ss Ls bels claims v rs in
       chain_sumcheck_consistent model \<and>
       chain_carry_consistent model \<and>
       chain_final_mle_x model \<and>
       chain_final_mle_y model)"
    by (simp add: production_verifier_accepts_def rust_hol_value_trace_relation_def
        rust_hol_trace_relation_def concrete_trace_relation_def executable_accepts_def)
  have chain: "verifier_chain_accepts
      (concrete_round_check P (concrete_finish_check final_claim wiring_rhs))
      (concrete_finish_relation (concrete_finish_check final_claim wiring_rhs))
      A ss Ls bels claims v rs"
    using verifier_chain_accepts_iff_trace[OF wf] observed by blast
  have local_bridge:
    "\<And>A s ss L Ls b bs claims v rs.
       gkr_chain_wf (s # ss) (L # Ls) (b # bs) \<Longrightarrow>
       concrete_round_check P (concrete_finish_check final_claim wiring_rhs) A
         (s # ss) (L # Ls) (b # bs) claims v rs \<Longrightarrow>
       concrete_finish_relation (concrete_finish_check final_claim wiring_rhs) A
         (s # ss) (L # Ls) (b # bs) claims v rs \<Longrightarrow>
       true_carry A s b rs \<Longrightarrow>
       true_polynomial_sumcheck P A s L b claims v rs"
    by (rule concrete_checks_supply_local_bridge)
  show ?thesis
    by (rule verifier_acceptance_implies_gkr_chain_bad[OF wf local_bridge chain])
qed

text \<open>
  The reverse direction is intentionally false as a refinement claim.
  The final corollary is a CANDIDATE refinement until the explicit
  <open>rust_hol_value_trace_relation<close> is discharged against the exact
  Rust/Creusot trace, final running claim, wiring RHS, and off-cube polynomial
  representation.  The former <open>local_bridge<close> is no
  longer a premise: <open>verifier_sumcheck_trace_refines_sumcheck<close> and
  <open>concrete_checks_supply_local_bridge<close> derive it from the finish-evaluation
  part of that representation relation.  The remaining relation is an
  ordinary theorem premise, not an axiom, and is deliberately load-bearing.

  The reverse direction is false: gkr_chain_bad does not mention the
  request/public-input guards.  Therefore even an inhabited model bad event
  cannot authorize executable acceptance when the production public-input
  binding fails.
\<close>

lemma gkr_chain_bad_does_not_imply_public_input_acceptance:
  assumes "gkr_chain_bad P A ss Ls bels claims v rs"
  shows "\<not> production_verifier_accepts
    (honest_acceptance_trace\<lparr>public_inputs_bound := False\<rparr>)"
  by (simp add: production_verifier_accepts_def executable_accepts_def
      honest_acceptance_trace_def)

end

end
