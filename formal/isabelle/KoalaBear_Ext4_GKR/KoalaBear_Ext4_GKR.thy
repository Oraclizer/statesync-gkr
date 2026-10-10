theory KoalaBear_Ext4_GKR
  imports KoalaBear_Ext4_Lift.KoalaBear_Ext4_Lift
begin

section \<open>Exact quartic GKR instance\<close>

text \<open>
  This stage owns only the exact-field instantiation of the existing GKR
  soundness theorem and the explicitly conditional uniform-coefficient
  pushforward. It imports only the lifting session. It does not verify Fiat--Shamir or random
  oracle soundness, Poseidon2 or challenger pseudorandomness, the p3 field
  implementation, whole-program Rust behavior, knowledge soundness, zero
  knowledge, an external wrapper, a receipt, settlement, or deployment.
\<close>

lemma gkr_layer_sumcheck_mpoly_ext4:
  "gkr_layer_sumcheck
     (vars :: koala_bear_ext4 mpoly \<Rightarrow> nat set) total_degree
     (\<lambda>p \<sigma>. insertion (the \<circ> \<sigma>) p) inst"
  by unfold_locales (auto simp add: multi_variate_polynomial_lemmas)

interpretation gkr4: gkr_layer_sumcheck
  "vars :: koala_bear_ext4 mpoly \<Rightarrow> nat set" total_degree
  "\<lambda>p \<sigma>. insertion (the \<circ> \<sigma>) p" inst
  by (rule gkr_layer_sumcheck_mpoly_ext4)

lemmas gkr_assembly_soundness_ext4 =
  gkr_layer_sumcheck.gkr_assembly_soundness[
    OF gkr_layer_sumcheck_mpoly_ext4]

lemmas gkr_assembly_soundness_deg4_ext4 =
  gkr_layer_sumcheck.gkr_assembly_soundness[
    OF gkr_layer_sumcheck_mpoly_ext4, where dbnd="\<lambda>_. 4"]

lemma ext4_denominator_exact:
  "real CARD(koala_bear_ext4) = real (2130706433 ^ 4)"
  by (simp add: CARD_koala_bear_ext4)

section \<open>Conditional uniform coefficient tuples\<close>

definition coeff4 ::
  "koala_bear \<times> koala_bear \<times> koala_bear \<times> koala_bear
   \<Rightarrow> koala_bear_ext4" where
  "coeff4 t = (case t of (a0,a1,a2,a3) \<Rightarrow> KBE (KBQ a0 a2) (KBQ a1 a3))"

lemma coeff4_bij: "bij coeff4"
proof (rule bijI)
  show "inj coeff4"
    apply (rule injI)
    subgoal for x y
      apply (cases x rule: prod_cases4)
      apply (cases y rule: prod_cases4)
      apply (simp add: coeff4_def)
      done
    done
  show "surj coeff4"
    apply (rule surjI[where f =
      "\<lambda>z. (q0 (e0 z), q0 (e1 z), q1 (e0 z), q1 (e1 z))"])
    subgoal for z
      apply (cases z)
      subgoal for x y
        apply (cases x)
        subgoal for a0 a2
          apply (cases y)
          subgoal for a1 a3
            by (simp add: coeff4_def)
          done
        done
      done
    done
qed

lemma uniform_coeff_tuple_pushforward:
  "map_pmf coeff4
     (pmf_of_set
       (UNIV :: (koala_bear \<times> koala_bear \<times> koala_bear \<times> koala_bear) set))
   = pmf_of_set (UNIV :: koala_bear_ext4 set)"
proof (rule map_pmf_of_set_bij_betw)
  show "bij_betw coeff4
    (UNIV :: (koala_bear \<times> koala_bear \<times> koala_bear \<times> koala_bear) set)
    (UNIV :: koala_bear_ext4 set)"
    using coeff4_bij by (simp add: bij_betw_def bij_def)
  show "(UNIV ::
    (koala_bear \<times> koala_bear \<times> koala_bear \<times> koala_bear) set) \<noteq> {}"
    by simp
  show "finite (UNIV ::
    (koala_bear \<times> koala_bear \<times> koala_bear \<times> koala_bear) set)"
    by simp
qed

text \<open>
  The preceding theorem is conditional on the source tuple having the stated
  uniform distribution. It does not prove that the Rust transcript or
  Poseidon2 duplex produces four independent uniform base-field coefficients.
\<close>

end
