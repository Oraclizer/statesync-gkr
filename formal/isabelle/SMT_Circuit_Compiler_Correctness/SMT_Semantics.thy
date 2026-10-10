(*
  Title:   SMT_Semantics.thy
  Session: SMT_Circuit_Compiler_Correctness (SMT-specific layer)

  The NATIVE verification semantics of sparse-Merkle-tree operations:
  the meaning standard Theorem A compares the compiled circuit against.

  This is the mechanized counterpart of `smt_valid_native`
  (crate `ssgkr-compiler`, `smt.rs`) - the three clauses below MUST stay
  literally in sync with the Rust transcription (which in turn was
  transcribed from the 1b spec sketch of this theory).

  Rust refinement map (crate `ssgkr-compiler`):
    leaf_state       ~ LeafState        (Empty | Occupied payload | Tombstone)
    encode           ~ LeafState::encode (tag 0/1/2, then payload encoding)
    smt_params       ~ SmtParams { depth, leaf_max_fields }
    path_root        ~ MerklePath::compute_root's fold (key low bit first)
    path_ok          ~ compute_root + the length/range guards
    smt_op           ~ SmtOperation     (same three constructors)
    smt_valid        ~ smt_valid_native (same three clauses)

  Modeling notes:
  - h_leaf / h_node are ABSTRACT locale parameters (the swappable hash
    seam; the concrete pair is Poseidon2, a plonky3 black box).
    The structural decomposition h_leaf = sponge o leaf_fold and
    its injectivity live in Leaf_Fold.thy (lemma (b)), NOT here.
  - The sketch's `empty_digest` parameter is dropped: smt_valid never
    consumes it (an unused locale parameter would be exactly the orphan-
    assumption defect class this development guards against).
*)

theory SMT_Semantics
  imports GKR_Protocol.Layered_Circuit
begin

section \<open>Leaf states and their field encoding\<close>

datatype 'v leaf_state =
    Empty
  | Occupied 'v
  | Tombstone

text \<open>
  Domain-separated encoding: a one-element kind tag (0 = Empty,
  1 = Occupied, 2 = Tombstone) followed by the payload encoding for
  \<open>Occupied\<close>.  The payload encoder is a parameter (the registry contract
  fixes the concrete convention; the prover is generic in it).
\<close>

fun encode :: "('v \<Rightarrow> 'f list) \<Rightarrow> 'v leaf_state \<Rightarrow> 'f::comm_ring_1 list" where
  "encode encp Empty = [0]"
| "encode encp (Occupied v) = 1 # encp v"
| "encode encp Tombstone = [2]"

lemma encode_nonempty: "encode encp l \<noteq> []"
  by (cases l) simp_all

lemma encode_tag_separates:
  \<comment> \<open>The tag lane alone separates the three states (\<open>2 \<noteq> 0\<close> and \<open>2 \<noteq> 1\<close>
     require odd characteristic; KoalaBear has odd characteristic. We keep
     the lemma over a ring with the needed inequalities as explicit
     premises, discharged trivially in concrete instances.)\<close>
  fixes encp :: "'v \<Rightarrow> 'f::comm_ring_1 list"
  assumes "(2 :: 'f) \<noteq> 0" "(2 :: 'f) \<noteq> 1"
  shows "hd (encode encp Empty) \<noteq> hd (encode encp Tombstone)"
    and "hd (encode encp (Occupied v)) \<noteq> hd (encode encp Tombstone)"
    and "hd (encode encp Empty) \<noteq> hd (encode encp (Occupied v))"
  using assms by simp_all

section \<open>Instance parameters\<close>

record smt_params =
  depth :: nat                \<comment> \<open>tree depth; Rust default 24 (genesis parameter)\<close>
  leaf_max_fields :: nat      \<comment> \<open>structural bound of the leaf hash domain\<close>

type_synonym asset_id = nat
  \<comment> \<open>Sequential AssetID key (monotone counter from the RWA Registry).
     Uniqueness is enforced by the verified state transition, not here.\<close>

section \<open>SMT semantics locale\<close>

locale smt_semantics =
  fixes params :: smt_params
    and h_leaf :: "'v leaf_state \<Rightarrow> 'd"
    and h_node :: "'d \<Rightarrow> 'd \<Rightarrow> 'd"
begin

text \<open>
  Merkle path verification: recompute the root from a leaf digest, the
  key bits (low bit = deepest level) and the sibling chain.
  Rust: \<open>MerklePath::compute_root\<close> - spec-literal transcription.
\<close>

fun path_root :: "'d \<Rightarrow> nat \<Rightarrow> 'd list \<Rightarrow> 'd" where
  "path_root leaf key [] = leaf"
| "path_root leaf key (s # ss) =
     path_root (if key mod 2 = 0 then h_node leaf s else h_node s leaf)
               (key div 2) ss"

definition path_ok :: "'v leaf_state \<Rightarrow> asset_id \<Rightarrow> 'd list \<Rightarrow> 'd \<Rightarrow> bool" where
  "path_ok leaf key siblings root \<longleftrightarrow>
     length siblings = depth params \<and>
     key < 2 ^ depth params \<and>
     path_root (h_leaf leaf) key siblings = root"

section \<open>Operation semantics: the meaning standard for Theorem A\<close>

end

datatype 'v smt_op =
    Membership asset_id 'v
  | NonMembership asset_id
  | Update asset_id "'v leaf_state" "'v leaf_state"
  \<comment> \<open>Rust: \<open>SmtOperation\<close> - same three constructors\<close>

context smt_semantics
begin

text \<open>
  \<open>smt_valid\<close>: what it MEANS for an operation to hold between two roots
  with a witness (leaf state + sibling chain).  This is the single
  semantic anchor; the compiled circuit is verified AGAINST this meaning,
  never against itself.  Clauses literally in sync with
  \<open>smt_valid_native\<close> (smt.rs).
\<close>

fun smt_valid :: "'v smt_op \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> ('v leaf_state \<times> 'd list) \<Rightarrow> bool" where
  "smt_valid (Membership k v) root root' (leaf, sib) \<longleftrightarrow>
     root' = root \<and> leaf = Occupied v \<and> path_ok leaf k sib root"
| "smt_valid (NonMembership k) root root' (leaf, sib) \<longleftrightarrow>
     root' = root \<and> (leaf = Empty \<or> leaf = Tombstone) \<and> path_ok leaf k sib root"
| "smt_valid (Update k old new) root root' (leaf, sib) \<longleftrightarrow>
     leaf = old \<and> path_ok old k sib root \<and> path_ok new k sib root'"
  \<comment> \<open>Update re-uses the SAME sibling chain for the old and new root:
     single-leaf update semantics.  Batched multi-leaf updates compose
     sequentially (Theorem D territory).\<close>

end

section \<open>Sanity instance (non-vacuity witness)\<close>

text \<open>
  A depth-1 instance over the integers with a transparent "hash"
  (injective pairing on small naturals encoded as ints) witnessing that
  the locale is inhabited and \<open>smt_valid\<close> actually discriminates: a valid
  membership holds and a mismatched root fails.
\<close>

definition toy_params :: smt_params where
  "toy_params = \<lparr> depth = 1, leaf_max_fields = 4 \<rparr>"

definition toy_h_leaf :: "int leaf_state \<Rightarrow> int" where
  "toy_h_leaf l = (case l of Empty \<Rightarrow> 0 | Occupied v \<Rightarrow> 100 + v | Tombstone \<Rightarrow> 1)"

definition toy_h_node :: "int \<Rightarrow> int \<Rightarrow> int" where
  "toy_h_node a b = 1000 + 65536 * a + b"

interpretation toy: smt_semantics toy_params toy_h_leaf toy_h_node
  by unfold_locales

lemma toy_membership_valid:
  "toy.smt_valid (Membership 0 7) (toy_h_node (toy_h_leaf (Occupied 7)) 3)
                 (toy_h_node (toy_h_leaf (Occupied 7)) 3)
                 (Occupied 7, [3])"
proof -
  have "toy.path_ok (Occupied 7) 0 [3] (toy_h_node (toy_h_leaf (Occupied 7)) 3)"
    unfolding toy.path_ok_def
    by (simp add: toy.path_root.simps toy_params_def)
  then show ?thesis by (simp add: toy.smt_valid.simps)
qed

lemma toy_membership_wrong_root_invalid:
  "\<not> toy.smt_valid (Membership 0 7) 42 42 (Occupied 7, [3])"
proof -
  have "\<not> toy.path_ok (Occupied 7) 0 [3] 42"
    unfolding toy.path_ok_def
    by (simp add: toy.path_root.simps toy_params_def
                  toy_h_node_def toy_h_leaf_def)
  then show ?thesis by (simp add: toy.smt_valid.simps)
qed

lemma toy_nonmembership_rejects_occupied:
  "\<not> toy.smt_valid (NonMembership 0) r r (Occupied 7, [3])"
  by (simp add: toy.smt_valid.simps)

end
