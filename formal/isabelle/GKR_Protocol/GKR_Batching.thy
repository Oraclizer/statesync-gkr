(*
  Title:   GKR_Batching.thy
  Session: GKR_Protocol (generic layer - no SMT / workload assumptions)

  Theorem D - Batching Correctness (generic).

  The v0.1 batching layer (crate `ssgkr-batching`, Module 3) amortizes
  prover cost by proving N witnesses of the same circuit kind as one
  batch over ONE shared compiled circuit (Module 1 caches the compiled
  structure per kind).  Note that in v0.1 the batch prover still
  generates ONE PROOF PER OPERATION: batching shares the circuit
  COMPILATION, not the proofs.  The semantic content of the v0.1 batch
  pipe is therefore exactly `map prove`, and Theorem D pins it: every
  proof in a batch verifies exactly as if produced by the single-proof
  pipeline on the same operation (the FV-CONTRACT comment on
  `BatchProver` in src/lib.rs).

  Rust refinement map (crate `ssgkr-batching`):
    'op            ~ ProveJob (kind + public inputs + witness)
    prove          ~ the injected single-proof path, applied to one job
                     (facade closure `prove_batch`; compile-once /
                     prove-many and the transcript convention live one
                     layer up, S-1 dependency direction)
    verify         ~ the single-proof verifier applied to (job, proof)
    batch_prove    ~ the proof generation of `BatchProver::prove_round`
                     for one drained batch (`BatchResult.proofs`,
                     aligned with the drained jobs in queue order)
    batch_verify   ~ element-wise verification of a `BatchResult`
    batch_pipeline ~ the `prove_batch` injection surface: ANY batch
                     prover whose per-job proofs equal the single-proof
                     path re-instantiates this locale (v0.2 amortized
                     prover; no-rework principle)

  Scope note (soundness surface): `BatchPolicy`, `DeadlineScheduler`
  and `WitnessQueue::drain` only decide WHICH operations form a batch
  (deadline remaining, queue length, amortization cap).  Theorem D
  quantifies over ALL operation lists, hence holds for every such
  scheduling decision; deadline and batch-size policy are deliberately
  OUTSIDE the model.  They are a liveness/performance surface, not a
  soundness surface (FV note on `DeadlineScheduler` in src/lib.rs:
  property-based tests carry that weight).

  Compile-cache harmlessness: the Module 1
  cache reuses one compiled circuit for every job of a kind.  In the
  model, `prove` is a FUNCTION of the operation alone, and
  `batch_prove = map prove` applies it independently per element:
  whether the circuit behind `prove` was compiled once per batch or
  once per job cannot change the value of `prove op`.  The cache is a
  structural optimisation of HOW `prove` is computed, never of WHAT it
  computes.  The lemmas `batch_prove_nth`,
  `batch_prove_context_independent` and
  `batch_prove_same_op_same_proof` are the formal residue of this
  independence (each batched proof depends on its own operation only,
  not on batch position, batch size, or neighbouring jobs).
*)

theory GKR_Batching
  imports Main
begin

section \<open>Abstract single-proof pipeline\<close>

text \<open>
  The batching crate is generic: it neither inspects proofs nor knows
  the GKR structure (the actual proving is injected as a closure).  We
  model the single-proof pipeline as an abstract proving function and
  an abstract verification predicate.  No locale assumptions are
  needed: determinism of both maps is automatic because HOL functions
  are functions, and Theorem D needs nothing else.
\<close>

locale gkr_batching =
  fixes prove  :: "'op \<Rightarrow> 'proof"
    and verify :: "'op \<Rightarrow> 'proof \<Rightarrow> bool"
begin

text \<open>
  The v0.1 batch prover: one proof per operation, in queue order
  (`BatchResult.proofs` aligned with the drained jobs).
\<close>

definition batch_prove :: "'op list \<Rightarrow> 'proof list" where
  "batch_prove ops = map prove ops"

text \<open>
  Batch verification: the proof list is aligned with the operation
  list, and every position verifies individually.  The length
  conjunct is the verifier-side counterpart of the alignment contract
  of `BatchResult`.
\<close>

definition batch_verify :: "'op list \<Rightarrow> 'proof list \<Rightarrow> bool" where
  "batch_verify ops proofs \<longleftrightarrow>
     length proofs = length ops \<and>
     (\<forall>i < length ops. verify (ops ! i) (proofs ! i))"

subsection \<open>Structural lemmas (cache harmlessness, formally)\<close>

lemma batch_prove_length [simp]:
  "length (batch_prove ops) = length ops"
  by (simp add: batch_prove_def)

text \<open>
  Position \<open>i\<close> of a batch carries the proof of operation \<open>i\<close> and of
  nothing else: batched proving is element-wise the single-proof path.
\<close>

lemma batch_prove_nth [simp]:
  "i < length ops \<Longrightarrow> batch_prove ops ! i = prove (ops ! i)"
  by (simp add: batch_prove_def)

text \<open>
  Batch-context independence: an operation's proof does not depend on
  the jobs batched before or after it (so the scheduler's choice of
  batch boundaries cannot alter any proof).
\<close>

lemma batch_prove_context_independent:
  "batch_prove (pre @ op # post) ! length pre = prove op"
  by (simp add: batch_prove_def nth_append)

text \<open>
  Two occurrences of the same operation receive the same proof - the
  observable consequence of sharing one compiled circuit per kind.
\<close>

lemma batch_prove_same_op_same_proof:
  "\<lbrakk> i < length ops; j < length ops; ops ! i = ops ! j \<rbrakk>
   \<Longrightarrow> batch_prove ops ! i = batch_prove ops ! j"
  by simp

subsection \<open>Interface lemmas for batch verification\<close>

lemma batch_verify_length:
  "batch_verify ops proofs \<Longrightarrow> length proofs = length ops"
  by (simp add: batch_verify_def)

text \<open>
  A verified batch verifies at every position (the consumption
  interface for downstream soundness composition: any single claim can
  be extracted from a verified batch).
\<close>

lemma batch_verify_imp_each:
  "\<lbrakk> batch_verify ops proofs; i < length ops \<rbrakk>
   \<Longrightarrow> verify (ops ! i) (proofs ! i)"
  by (simp add: batch_verify_def)

text \<open>Equivalent pointwise characterisation via @{const list_all2}.\<close>

lemma batch_verify_conv_list_all2:
  "batch_verify ops proofs \<longleftrightarrow> list_all2 verify ops proofs"
  by (auto simp: batch_verify_def list_all2_conv_all_nth)

subsection \<open>Theorem D - batching correctness\<close>

text \<open>
  (i) A batch of honestly produced proofs verifies iff every operation
  verifies under the single-proof pipeline.  Note the right-hand side
  ranges over the SET of operations: since proving is a function of
  the operation alone, duplicates cannot make a batch behave
  differently from its underlying set of claims.
\<close>

theorem theorem_D_batching_correctness:
  "batch_verify ops (batch_prove ops) \<longleftrightarrow>
     (\<forall>op \<in> set ops. verify op (prove op))"
  by (simp add: batch_verify_def all_set_conv_all_nth)

text \<open>
  (ii) Individual result preservation: the verification outcome of the
  \<open>i\<close>-th batched proof coincides with the outcome the single-proof
  pipeline delivers for that operation - acceptances and rejections
  are preserved position by position, whatever the rest of the batch
  does.
\<close>

theorem theorem_D_individual_preservation:
  assumes "i < length ops"
  shows "verify (ops ! i) (batch_prove ops ! i) \<longleftrightarrow>
           verify (ops ! i) (prove (ops ! i))"
  using assms by simp

corollary theorem_D_accept_preservation:
  "\<lbrakk> i < length ops; verify (ops ! i) (prove (ops ! i)) \<rbrakk>
   \<Longrightarrow> verify (ops ! i) (batch_prove ops ! i)"
  by simp

corollary theorem_D_reject_preservation:
  "\<lbrakk> i < length ops; \<not> verify (ops ! i) (prove (ops ! i)) \<rbrakk>
   \<Longrightarrow> \<not> verify (ops ! i) (batch_prove ops ! i)"
  by simp

text \<open>
  (iii) Compile-cache harmlessness is not a separate proposition in
  this model but a consequence of its shape: \<open>batch_prove\<close> IS \<open>map
  prove\<close> (definitionally), so reusing one compiled circuit across a
  batch cannot be observed by any verifier.  The lemmas
  @{thm [source] batch_prove_nth},
  @{thm [source] batch_prove_context_independent} and
  @{thm [source] batch_prove_same_op_same_proof} state the observable
  content: each proof is determined by its own operation only.
\<close>

end

section \<open>Parameterised batch pipe - the re-instantiation surface\<close>

text \<open>
  v0.1 proves per operation; a v0.2 amortized batch prover may compute
  the proof list differently (shared preprocessing, reordered
  evaluation, fused transcripts...).  To keep Theorem D reusable
  WITHOUT rework, the batch pipe itself is a locale parameter: any
  pipe that (a) preserves length and (b) delivers at every position
  the proof of the single-proof path inherits all of Theorem D by a
  single interpretation.  This mirrors the Rust structure, where the
  actual proving is INJECTED into \<open>BatchProver::prove_round\<close> as the
  \<open>prove_batch\<close> closure; the two locale assumptions are precisely the
  contract that closure must meet.
\<close>

locale batch_pipeline = gkr_batching prove verify
  for prove :: "'op \<Rightarrow> 'proof" and verify :: "'op \<Rightarrow> 'proof \<Rightarrow> bool" +
  fixes batch_pipe :: "'op list \<Rightarrow> 'proof list"
  assumes batch_pipe_length: "length (batch_pipe ops) = length ops"
    and batch_pipe_nth: "i < length ops \<Longrightarrow> batch_pipe ops ! i = prove (ops ! i)"
begin

text \<open>Any conforming pipe is extensionally the v0.1 pipe.\<close>

lemma batch_pipe_eq_batch_prove:
  "batch_pipe ops = batch_prove ops"
  by (rule nth_equalityI) (simp_all add: batch_pipe_length batch_pipe_nth)

theorem theorem_D_pipe_batching_correctness:
  "batch_verify ops (batch_pipe ops) \<longleftrightarrow>
     (\<forall>op \<in> set ops. verify op (prove op))"
  by (simp add: batch_pipe_eq_batch_prove theorem_D_batching_correctness)

theorem theorem_D_pipe_individual_preservation:
  assumes "i < length ops"
  shows "verify (ops ! i) (batch_pipe ops ! i) \<longleftrightarrow>
           verify (ops ! i) (prove (ops ! i))"
  using assms by (simp add: batch_pipe_nth)

end

text \<open>
  The v0.1 batch prover is itself an instance of the parameterised
  surface: `map prove` discharges both pipe obligations definitionally.
  Registered as a sublocale, every interpretation of @{locale
  gkr_batching} automatically carries the pipe-level theorems for the
  v0.1 pipe (qualifier \<open>v01\<close>).
\<close>

sublocale gkr_batching \<subseteq> v01: batch_pipeline prove verify batch_prove
  by unfold_locales simp_all

section \<open>Activation instance (N = 2, accept/reject mixed)\<close>

text \<open>
  A concrete, non-vacuous instance: proofs are squares, and the
  verifier additionally rejects the operation \<open>0\<close>, so honest proving
  does NOT imply acceptance - both outcomes occur.  The batch \<open>[3, 0]\<close>
  exercises Theorem D on a mixed batch: position 0 accepts exactly as
  a single proof, position 1 rejects exactly as a single proof, and
  the whole-batch conjunction rejects.
\<close>

definition demo_prove :: "nat \<Rightarrow> nat" where
  "demo_prove n = n * n"

definition demo_verify :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "demo_verify n p \<longleftrightarrow> p = n * n \<and> 0 < n"

interpretation demo: gkr_batching demo_prove demo_verify
  by unfold_locales

text \<open>Single-proof pipeline: acceptance and rejection both inhabited.\<close>

lemma demo_accepts_3: "demo_verify 3 (demo_prove 3)"
  by (simp add: demo_verify_def demo_prove_def)

lemma demo_rejects_0: "\<not> demo_verify 0 (demo_prove 0)"
  by (simp add: demo_verify_def demo_prove_def)

lemma demo_rejects_wrong_proof: "\<not> demo_verify 3 10"
  by (simp add: demo_verify_def)

text \<open>The mixed batch \<open>[3, 0]\<close>: concrete proof vector.\<close>

lemma demo_batch_proofs: "demo.batch_prove [3, 0] = [9, 0]"
  by (simp add: demo.batch_prove_def demo_prove_def)

text \<open>Position-wise preservation activates on both outcomes.\<close>

lemma demo_mixed_position_0_accepts:
  "demo_verify 3 (demo.batch_prove [3, 0] ! 0)"
  by (simp add: demo_batch_proofs demo_verify_def)

lemma demo_mixed_position_1_rejects:
  "\<not> demo_verify 0 (demo.batch_prove [3, 0] ! 1)"
  by (simp add: demo_batch_proofs demo_verify_def)

text \<open>The whole mixed batch rejects (one bad claim suffices) ...\<close>

lemma demo_mixed_batch_rejects:
  "\<not> demo.batch_verify [3, 0] (demo.batch_prove [3, 0])"
  by (simp add: demo.theorem_D_batching_correctness demo_verify_def demo_prove_def)

text \<open>... while an all-honest, all-valid batch accepts.\<close>

lemma demo_all_accepting_batch:
  "demo.batch_verify [3, 5] (demo.batch_prove [3, 5])"
  by (simp add: demo.theorem_D_batching_correctness demo_verify_def demo_prove_def)

text \<open>Batch verification is not vacuous on malformed inputs either.\<close>

lemma demo_length_mismatch_rejects:
  "\<not> demo.batch_verify [3] []"
  by (simp add: demo.batch_verify_def)

lemma demo_forged_batch_rejects:
  "\<not> demo.batch_verify [3, 5] [9, 26]"
  by (simp add: demo.batch_verify_conv_list_all2 demo_verify_def)

subsection \<open>Re-instantiation demo (the v0.2 path)\<close>

text \<open>
  A pipe that processes the batch in REVERSE order and restores order
  afterwards is extensionally the honest pipe, so it inherits Theorem
  D through the two pointwise obligations alone.  This is the
  no-rework path a v0.2 amortized prover takes: discharge (a) length
  preservation and (b) pointwise agreement with the single-proof
  path, inherit every theorem of @{locale batch_pipeline}.
\<close>

definition demo_rev_pipe :: "nat list \<Rightarrow> nat list" where
  "demo_rev_pipe ops = rev (map demo_prove (rev ops))"

lemma demo_rev_pipe_eq_map:
  "demo_rev_pipe ops = map demo_prove ops"
  by (simp add: demo_rev_pipe_def rev_map)

interpretation demo_rev: batch_pipeline demo_prove demo_verify demo_rev_pipe
  by unfold_locales (simp_all add: demo_rev_pipe_eq_map)

lemma demo_rev_pipe_mixed_batch_rejects:
  "\<not> demo.batch_verify [3, 0] (demo_rev_pipe [3, 0])"
  by (simp add: demo_rev.theorem_D_pipe_batching_correctness
                demo_verify_def demo_prove_def)

lemma demo_rev_pipe_position_0_accepts:
  "demo_verify 3 (demo_rev_pipe [3, 0] ! 0)"
  by (simp add: demo_rev_pipe_eq_map demo_verify_def demo_prove_def)

section \<open>The amortized batch pipe (v0.2) - shared prepared state\<close>

text \<open>
  The v0.2 throughput batch prover amortizes the per-batch setup - circuit
  compilation and the verifier's wiring derivation - into a PREPARED state
  built once per operation kind (crate root: \<open>PreparedSync\<close>,
  \<open>prove_batch_prepared\<close>, \<open>prove_batch_parallel\<close>; the batch semantics
  decision record lives in the repository under \<open>docs/adr/\<close>), and may
  evaluate the per-job proofs on any order-restoring parallel schedule.

  The model content of that design is a single assumption: proving
  against the shared prepared state IS the single-proof pipeline, job by
  job (\<open>prove_with prep = prove\<close>). The executable counterpart is pinned
  bit-for-bit by the agreement tests in \<open>tests/batch_v02.rs\<close> (prepared
  and parallel proofs equal the single-path proofs across operation
  kinds, batch sizes and worker counts). Everything else is inherited:
  both v0.2 pipes discharge the two @{locale batch_pipeline} obligations
  and carry all of Theorem D without re-proving anything.
\<close>

locale gkr_batching_v02 = gkr_batching prove verify
  for prove :: "'op \<Rightarrow> 'proof" and verify :: "'op \<Rightarrow> 'proof \<Rightarrow> bool" +
  fixes prep :: "'prep"
    and prove_with :: "'prep \<Rightarrow> 'op \<Rightarrow> 'proof"
  assumes prove_with_agrees: "prove_with prep op = prove op"
begin

text \<open>
  The amortized sequential pipe (\<open>prove_batch_prepared\<close>): one shared
  prepared state, one proof per job, queue order preserved.
\<close>

definition prepared_pipe :: "'op list \<Rightarrow> 'proof list" where
  "prepared_pipe ops = map (prove_with prep) ops"

text \<open>
  The parallel pipe (\<open>prove_batch_parallel\<close>): workers evaluate jobs
  independently and results are collected back IN INPUT ORDER. The
  index-driven form below mirrors that order-restoring collection.
  Scheduling - which worker computes which index, in what real-time
  order - has no counterpart in the function model, and that absence IS
  the determinism argument: each position's value is a function of its
  own operation alone, so worker count cannot reach any proof.
\<close>

definition parallel_pipe :: "'op list \<Rightarrow> 'proof list" where
  "parallel_pipe ops = map (\<lambda>i. prove_with prep (ops ! i)) [0..<length ops]"

lemma prepared_pipe_eq_map: "prepared_pipe ops = map prove ops"
  by (simp add: prepared_pipe_def prove_with_agrees)

lemma parallel_pipe_eq_map: "parallel_pipe ops = map prove ops"
proof -
  have "map (\<lambda>i. prove_with prep (ops ! i)) [0..<length ops]
      = map (prove_with prep) (map ((!) ops) [0..<length ops])"
    by (simp add: map_map o_def)
  also have "\<dots> = map (prove_with prep) ops"
    by (simp add: map_nth)
  finally show ?thesis
    by (simp add: parallel_pipe_def prove_with_agrees)
qed

text \<open>
  Both pipes re-instantiate the parameterised surface: the two pointwise
  obligations discharge from the agreement assumption alone, and every
  theorem of @{locale batch_pipeline} follows for the amortized prover.
\<close>

sublocale prepared: batch_pipeline prove verify prepared_pipe
  by unfold_locales (simp_all add: prepared_pipe_eq_map)

sublocale parallel: batch_pipeline prove verify parallel_pipe
  by unfold_locales (simp_all add: parallel_pipe_eq_map)

end

subsection \<open>Activation instance (v0.2 pipes on the mixed batch)\<close>

text \<open>
  Non-vacuity witness: the demo pipeline with an explicit (trivial)
  prepared state. The agreement assumption discharges by computation, and
  Theorem D activates on the same mixed batch as above through BOTH v0.2
  pipes - rejection at a bad position, acceptance of an all-valid batch.
\<close>

definition demo_prove_with :: "unit \<Rightarrow> nat \<Rightarrow> nat" where
  "demo_prove_with s n = n * n"

interpretation demo_v02: gkr_batching_v02 demo_prove demo_verify "()" demo_prove_with
  by unfold_locales (simp add: demo_prove_with_def demo_prove_def)

lemma demo_v02_prepared_mixed_batch_rejects:
  "\<not> demo.batch_verify [3, 0] (demo_v02.prepared_pipe [3, 0])"
  by (simp add: demo_v02.prepared.theorem_D_pipe_batching_correctness
                demo_verify_def demo_prove_def)

lemma demo_v02_parallel_position_0_accepts:
  "demo_verify 3 (demo_v02.parallel_pipe [3, 0] ! 0)"
  by (simp add: demo_v02.parallel_pipe_eq_map demo_verify_def demo_prove_def)

lemma demo_v02_parallel_all_valid_batch_accepts:
  "demo.batch_verify [3, 5] (demo_v02.parallel_pipe [3, 5])"
  by (simp add: demo_v02.parallel.theorem_D_pipe_batching_correctness
                demo_verify_def demo_prove_def)

end
