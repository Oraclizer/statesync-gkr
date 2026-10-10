(*
  Title:   Leaf_Fold.thy
  Session: SMT_Circuit_Compiler_Correctness (SMT-specific layer)

  The lossless leaf pre-image fold and its injectivity - lemma (b) of
  the correctness track: the purely combinatorial core of the leaf-hash
  collision-resistance argument.

  This theory is the mechanized counterpart of `leaf_fold` and
  `leaf_pre_width` (crate `ssgkr-primitives`, `hash.rs`); the layout
  MUST stay literally in sync with the Rust implementation:

    pre[0]        = enc[0]                 tag lane (domain separation)
    pre[1]        = of_nat (length enc)    length lane (injectivity)
    pre[2..len]   = enc[1..]               verbatim - no wrap, no sum
    pre[len+1..]  = 0                      zero padding
    width         = leaf_pre_width max
                  = div_ceil (max + 1) 8 * 8   (whole rate-8 blocks)

  Rust refinement map (crate `ssgkr-primitives`):
    LEAF_SPONGE_RATE ~ LEAF_SPONGE_RATE  (= 8)
    leaf_pre_width   ~ leaf_pre_width    (same div_ceil arithmetic)
    leaf_fold        ~ leaf_fold         (the Ok branch; the Err guards
                       correspond to the explicit domain premise
                       1 <= length enc <= leaf_max_fields here)
    leaf_fold_inj    ~ the FV-CONTRACT clause "injective over the
                       in-bound encoding domain" and the property test
                       leaf_fold_is_injective_on_in_bound_encodings

  Modeling notes:
  - Rust `leaf_fold` is PARTIAL (Err on empty or oversized encodings);
    the Isabelle function is total, so every statement carries the
    domain premise explicitly.  Nothing is claimed outside the Ok
    domain.
  - Injectivity of the length lane needs of_nat to be injective on
    {0..max_fields}.  Over an arbitrary finite ring this does
    NOT follow from max_fields < CARD('f) alone: in the product ring
    Z2 x Z2 (CARD = 4) one has of_nat 2 = of_nat 0 although 2 < 4.
    The premise is therefore stated directly as "of_nat is injective
    up to the bound" - the exact fact a PRIME field such as KoalaBear
    (p = 2^31 - 2^24 + 1, default bound 31 << p) discharges trivially,
    and characteristic-zero rings (the int firing instances below)
    discharge by simp.
  - Collision resistance of the sponge is neither assumed nor proven
    here.  The reduction theorem is purely structural: it turns any
    h_leaf collision on distinct in-bound encodings into an EXPLICIT
    sponge collision pair.  Hardness of sponge collisions is the
    plonky3 black-box boundary; this theory claims
    nothing about it.
*)

theory Leaf_Fold
  imports SMT_Semantics
begin

section \<open>Sponge geometry\<close>

text \<open>
  Rust: \<open>LEAF_SPONGE_RATE = 8\<close> - lanes absorbed per permutation of the
  rate-8 sponge.  The pre-image width is the encoding bound plus one
  bookkeeping lane (the length lane; the tag lane replaces \<open>enc[0]\<close>,
  it does not add width) rounded UP to whole rate blocks, so the
  sponge absorbs every lane in exact chunks.
\<close>

definition LEAF_SPONGE_RATE :: nat where
  "LEAF_SPONGE_RATE = 8"

text \<open>
  Rust: \<open>leaf_pre_width\<close> - literally
  \<open>(leaf_max_fields + 1).div_ceil(LEAF_SPONGE_RATE) * LEAF_SPONGE_RATE\<close>,
  with \<open>div_ceil\<close> unfolded to its standard-library definition
  \<open>d + (if r = 0 then 0 else 1)\<close> where \<open>d\<close>/\<open>r\<close> are quotient/remainder.
  (The Rust parameter name \<open>leaf_max_fields\<close> is taken by the
  \<open>smt_params\<close> record selector of \<open>SMT_Semantics\<close>, so the bound is
  named \<open>max_fields\<close> throughout this theory.)
\<close>

definition leaf_pre_width :: "nat \<Rightarrow> nat" where
  "leaf_pre_width max_fields =
     ((max_fields + 1) div LEAF_SPONGE_RATE
      + (if (max_fields + 1) mod LEAF_SPONGE_RATE = 0 then 0 else 1))
     * LEAF_SPONGE_RATE"

lemma leaf_pre_width_ge:
  "max_fields + 1 \<le> leaf_pre_width max_fields"
proof (cases "(max_fields + 1) mod 8 = 0")
  case True
  have "max_fields + 1
        = (max_fields + 1) div 8 * 8 + (max_fields + 1) mod 8"
    by simp
  with True show ?thesis
    by (simp add: leaf_pre_width_def LEAF_SPONGE_RATE_def)
next
  case False
  then have w: "leaf_pre_width max_fields
                = (max_fields + 1) div 8 * 8 + 8"
    by (simp add: leaf_pre_width_def LEAF_SPONGE_RATE_def algebra_simps)
  have "max_fields + 1
        = (max_fields + 1) div 8 * 8 + (max_fields + 1) mod 8"
    by simp
  moreover have "(max_fields + 1) mod 8 < 8" by simp
  ultimately show ?thesis using w by linarith
qed

lemma leaf_pre_width_rate_blocks:
  "leaf_pre_width max_fields mod LEAF_SPONGE_RATE = 0"
  \<comment> \<open>The sponge absorbs the pre-image in exact rate blocks (the Rust
     \<open>debug_assert\<close> in \<open>hash_leaf_pre\<close>).\<close>
  by (simp add: leaf_pre_width_def)

lemma leaf_pre_width_rounds_to_rate_blocks:
  \<comment> \<open>Pin against the Rust unit test \<open>leaf_pre_width_rounds_to_rate_blocks\<close>:
     31 + 1 bookkeeping lanes round to exactly four rate-8 blocks.\<close>
  "leaf_pre_width 31 = 32"
  "leaf_pre_width 7 = 8"
  "leaf_pre_width 15 = 16"
  "leaf_pre_width 23 = 24"
  by (simp_all add: leaf_pre_width_def LEAF_SPONGE_RATE_def)

section \<open>The lossless fold\<close>

text \<open>
  Rust: \<open>leaf_fold\<close> (hash.rs) - the fixed-width, lossless pre-image of
  an encoding of length \<open>1..leaf_max_fields\<close>.  The Rust Err branches
  (empty / oversized) are the domain premise here; on the Ok domain the
  layout is literally \<open>[tag, length, verbatim rest, zero padding]\<close>.
\<close>

definition leaf_fold :: "'f::comm_ring_1 list \<Rightarrow> nat \<Rightarrow> 'f list" where
  "leaf_fold enc max_fields =
     [enc ! 0, of_nat (length enc)]
     @ tl enc
     @ replicate (leaf_pre_width max_fields - (length enc + 1)) 0"

lemma leaf_fold_length:
  assumes len_lb: "1 \<le> length enc"
      and len_ub: "length enc \<le> max_fields"
  shows "length (leaf_fold enc max_fields) = leaf_pre_width max_fields"
proof -
  have "length enc + 1 \<le> leaf_pre_width max_fields"
    using len_ub leaf_pre_width_ge[of max_fields] by linarith
  with len_lb show ?thesis
    unfolding leaf_fold_def by simp
qed

subsection \<open>Lane layout (pin against the Rust test
  \<open>leaf_fold_layout_tag_len_verbatim\<close>)\<close>

lemma leaf_fold_tag_lane [simp]:
  "leaf_fold enc max_fields ! 0 = enc ! 0"
  by (simp add: leaf_fold_def)

lemma leaf_fold_length_lane [simp]:
  "leaf_fold enc max_fields ! 1 = of_nat (length enc)"
  by (simp add: leaf_fold_def)

lemma leaf_fold_verbatim_lane:
  assumes i: "i < length enc - 1"
  shows "leaf_fold enc max_fields ! (i + 2) = enc ! (i + 1)"
proof -
  have "leaf_fold enc max_fields ! Suc (Suc i)
        = (tl enc @ replicate (leaf_pre_width max_fields - (length enc + 1)) 0) ! i"
    by (simp add: leaf_fold_def)
  also have "\<dots> = tl enc ! i"
    using i by (simp add: nth_append)
  also have "\<dots> = enc ! Suc i"
    using i by (simp add: nth_tl)
  finally have "leaf_fold enc max_fields ! Suc (Suc i) = enc ! Suc i" .
  then show ?thesis by (simp add: eval_nat_numeral)
qed

lemma leaf_fold_pad_suffix:
  \<comment> \<open>Everything beyond the tag/length/verbatim prefix is the zero
     padding (the "zeros beyond" clause of the Rust layout test).
     Per-lane readings follow via @{thm nth_replicate}.\<close>
  assumes len_lb: "1 \<le> length enc"
  shows "drop (length enc + 1) (leaf_fold enc max_fields)
         = replicate (leaf_pre_width max_fields - (length enc + 1)) 0"
proof -
  have split: "leaf_fold enc max_fields
        = (enc ! 0 # of_nat (length enc) # tl enc)
          @ replicate (leaf_pre_width max_fields - (length enc + 1)) 0"
    by (simp add: leaf_fold_def)
  have len_pre: "length (enc ! 0 # of_nat (length enc) # tl enc)
        = length enc + 1"
    using len_lb by simp
  from split len_pre show ?thesis
    by (metis append_eq_conv_conj)
qed

section \<open>Injectivity (lemma (b))\<close>

text \<open>
  Distinct in-bound encodings never share a pre-image.  Proof route:
  the length lane forces equal lengths (via the \<open>of_nat\<close> premise), the
  padding then coincides, so the verbatim region and the tag lane pin
  every element (list extensionality).

  The \<open>of_nat\<close> premise is exactly what the length lane needs and no
  more: over KoalaBear it holds because the bound (default 31) is far
  below p; see the modeling notes in the file header for why it must
  be stated as injectivity-up-to-the-bound rather than
  \<open>max_fields < CARD('f)\<close>.
\<close>

theorem leaf_fold_inj:
  fixes e1 e2 :: "'f::comm_ring_1 list"
  assumes len1: "1 \<le> length e1" "length e1 \<le> max_fields"
      and len2: "1 \<le> length e2" "length e2 \<le> max_fields"
      and of_nat_inj: "\<And>a b. \<lbrakk> a \<le> max_fields; b \<le> max_fields;
                               (of_nat a :: 'f) = of_nat b \<rbrakk> \<Longrightarrow> a = b"
      and eq: "leaf_fold e1 max_fields = leaf_fold e2 max_fields"
  shows "e1 = e2"
proof -
  have ne1: "e1 \<noteq> []" and ne2: "e2 \<noteq> []"
    using len1(1) len2(1) by auto
  \<comment> \<open>Lane 0: the tag.\<close>
  have tag: "e1 ! 0 = e2 ! 0"
    using eq unfolding leaf_fold_def by simp
  \<comment> \<open>Lane 1: the length lane, then the \<open>of_nat\<close> premise.\<close>
  have lenlane: "(of_nat (length e1) :: 'f) = of_nat (length e2)"
    using eq unfolding leaf_fold_def by simp
  have len_eq: "length e1 = length e2"
    by (rule of_nat_inj[OF len1(2) len2(2) lenlane])
  \<comment> \<open>Lanes 2..: verbatim region plus identical padding.\<close>
  have rest: "tl e1 @ replicate (leaf_pre_width max_fields - (length e1 + 1)) 0
            = tl e2 @ replicate (leaf_pre_width max_fields - (length e2 + 1)) 0"
    using eq unfolding leaf_fold_def by simp
  from rest len_eq have tl_eq: "tl e1 = tl e2" by simp
  \<comment> \<open>List extensionality.\<close>
  obtain a1 t1 where e1c: "e1 = a1 # t1" using ne1 by (cases e1) auto
  obtain a2 t2 where e2c: "e2 = a2 # t2" using ne2 by (cases e2) auto
  from tag e1c e2c have "a1 = a2" by simp
  moreover from tl_eq e1c e2c have "t1 = t2" by simp
  ultimately show "e1 = e2" using e1c e2c by simp
qed

section \<open>Collision-resistance reduction\<close>

text \<open>
  The structural seam \<open>h_leaf = sponge o leaf_fold\<close> on the in-bound
  domain (Rust: \<open>HashGadget::hash_leaf = hash_leaf_pre o leaf_fold\<close>;
  the equation is restricted to the Ok domain because Rust \<open>hash_leaf\<close>
  errs outside it).  The sponge is a fully abstract parameter: no
  collision-resistance assumption is placed on it.  The reduction
  turns an \<open>h_leaf\<close> collision on distinct in-bound encodings into an
  explicit sponge collision pair, which is precisely the interface
  the system-level "root binds state" interpretation consumes
  (Poseidon2 hardness stays a black-box assumption).
\<close>

locale leaf_hash_structure =
  fixes h_leaf :: "'f::comm_ring_1 list \<Rightarrow> 'd"
    and sponge :: "'f list \<Rightarrow> 'd"
    and max_fields :: nat
  assumes h_leaf_decomp:
      "\<And>enc. \<lbrakk> 1 \<le> length enc; length enc \<le> max_fields \<rbrakk>
             \<Longrightarrow> h_leaf enc = sponge (leaf_fold enc max_fields)"
    and of_nat_inj_bound:
      "\<And>a b. \<lbrakk> a \<le> max_fields; b \<le> max_fields;
               (of_nat a :: 'f) = of_nat b \<rbrakk> \<Longrightarrow> a = b"
begin

theorem h_leaf_collision_to_sponge_collision:
  assumes e1: "1 \<le> length e1" "length e1 \<le> max_fields"
      and e2: "1 \<le> length e2" "length e2 \<le> max_fields"
      and neq: "e1 \<noteq> e2"
      and collide: "h_leaf e1 = h_leaf e2"
  shows "\<exists>p1 p2. p1 \<noteq> p2 \<and> sponge p1 = sponge p2"
proof -
  have fold_neq: "leaf_fold e1 max_fields \<noteq> leaf_fold e2 max_fields"
  proof
    assume feq: "leaf_fold e1 max_fields = leaf_fold e2 max_fields"
    have "e1 = e2"
    proof (rule leaf_fold_inj[OF e1 e2 _ feq])
      fix a b
      assume "a \<le> max_fields" and "b \<le> max_fields"
        and "(of_nat a :: 'f) = of_nat b"
      then show "a = b" by (rule of_nat_inj_bound)
    qed
    with neq show False ..
  qed
  have "sponge (leaf_fold e1 max_fields) = sponge (leaf_fold e2 max_fields)"
    using collide h_leaf_decomp[OF e1] h_leaf_decomp[OF e2] by simp
  with fold_neq show ?thesis by blast
qed

end

subsection \<open>The encode domain\<close>

text \<open>
  Bridge to the leaf-state encoding of \<open>SMT_Semantics\<close>: every \<open>encode\<close>
  result is nonempty (tag lane first), and it stays within the bound
  whenever the payload encoder respects it - so encoded leaf states
  live in the injectivity domain of the fold.
\<close>

lemma encode_length_lb: "1 \<le> length (encode encp l)"
  by (cases l) simp_all

lemma encode_length_ub:
  assumes "\<And>v. 1 + length (encp v) \<le> max_fields"
      and "1 \<le> max_fields"
  shows "length (encode encp l) \<le> max_fields"
  using assms by (cases l) simp_all

context leaf_hash_structure
begin

corollary encoded_state_collision_to_sponge_collision:
  \<comment> \<open>Leaf-state level reading of the reduction: two leaf states whose
     encodings differ (e.g. any two distinct states under an injective
     payload encoder) cannot collide under \<open>h_leaf\<close> without exhibiting a
     sponge collision.\<close>
  fixes encp :: "'v \<Rightarrow> 'f list"
  assumes encp_bound: "\<And>v. 1 + length (encp v) \<le> max_fields"
      and max_pos: "1 \<le> max_fields"
      and neq: "encode encp l1 \<noteq> encode encp l2"
      and collide: "h_leaf (encode encp l1) = h_leaf (encode encp l2)"
  shows "\<exists>p1 p2. p1 \<noteq> p2 \<and> sponge p1 = sponge p2"
  by (rule h_leaf_collision_to_sponge_collision[OF
        encode_length_lb encode_length_ub[OF encp_bound max_pos]
        encode_length_lb encode_length_ub[OF encp_bound max_pos]
        neq collide])

end

section \<open>Firing instances (non-vacuity witnesses)\<close>

text \<open>
  The theorems actually fire.  The \<open>of_nat\<close> premise is discharged over a
  characteristic-zero ring (int, by simp); over the concrete KoalaBear
  prime field it holds because the bound (default 31) is far below
  \<open>p = 2^31 - 2^24 + 1\<close> (discharged at instantiation).
\<close>

lemma leaf_fold_inj_int:
  fixes e1 e2 :: "int list"
  assumes "1 \<le> length e1" "length e1 \<le> max_fields"
      and "1 \<le> length e2" "length e2 \<le> max_fields"
      and "leaf_fold e1 max_fields = leaf_fold e2 max_fields"
  shows "e1 = e2"
  by (rule leaf_fold_inj[OF assms(1,2,3,4) _ assms(5)]) simp

lemma leaf_fold_inj_fires:
  \<comment> \<open>A pre-image determines its in-bound encoding uniquely.\<close>
  fixes e :: "int list"
  assumes "1 \<le> length e" and "length e \<le> 31"
      and "leaf_fold e 31 = leaf_fold [1, 42] 31"
  shows "e = [1, 42]"
  by (rule leaf_fold_inj_int[OF assms(1,2) _ _ assms(3)]) simp_all

subsection \<open>The two collision classes the fold closes\<close>

text \<open>
  (a) The wrap-collision class (the audited CRITICAL break).  The
  pre-fix fold wrapped the encoding onto 16 lanes additively
  (\<open>s[1 + (j mod 15)] += v\<close>), so encodings agreeing on all wrap-slot
  SUMS shared a pre-image: below, rest positions 0 and 15 landed in
  the same slot and 5 + 0 = 3 + 2.  The lossless fold separates the
  pair in the first verbatim lane.  (Pin against the Rust property
  test, class (a).)
\<close>

definition former_wrap_a :: "int list" where
  "former_wrap_a = 1 # 5 # replicate 14 0 @ [0]"

definition former_wrap_b :: "int list" where
  "former_wrap_b = 1 # 3 # replicate 14 0 @ [2]"

lemma former_wrap_class_separated:
  "former_wrap_a \<noteq> former_wrap_b"
  "leaf_fold former_wrap_a 31 \<noteq> leaf_fold former_wrap_b 31"
  by (simp_all add: former_wrap_a_def former_wrap_b_def leaf_fold_def)

text \<open>
  (b) The trailing-zero / length-shift class - the reason the length
  lane exists.  \<open>[1, 7]\<close> and \<open>[1, 7, 0]\<close> agree on the tag lane and on
  the whole verbatim-plus-padding region; ONLY the length lane
  separates their pre-images.  Without it the fold would identify
  them, and \<open>h_leaf\<close> would collide without any sponge collision - the
  forgery class of the audit.  (Pin against the Rust property test,
  class (b).)
\<close>

lemma zero_extension_class_separated:
  "leaf_fold [1, 7] 31 \<noteq> (leaf_fold [1, 7, 0] 31 :: int list)"
  by (simp add: leaf_fold_def)

subsection \<open>The reduction fires\<close>

text \<open>
  With a toy, deliberately WEAK sponge (the lane sum) an \<open>h_leaf\<close>
  collision on distinct in-bound encodings materializes an explicit
  sponge collision pair: \<open>[1, 5, 0]\<close> and \<open>[1, 3, 2]\<close> have equal lane
  sums, and by injectivity their pre-images are distinct - exactly
  such a pair.  Note what this shows: the reduction places NO
  collision-resistance assumption on the sponge; hardness lives in
  the Poseidon2 black box, structure lives here.
\<close>

interpretation toy_leaf_hash: leaf_hash_structure
  "\<lambda>enc. sum_list (leaf_fold enc 31)" "sum_list :: int list \<Rightarrow> int" 31
  by unfold_locales simp_all

lemma toy_sponge_collision_exhibited:
  "\<exists>p1 p2 :: int list. p1 \<noteq> p2 \<and> sum_list p1 = sum_list p2"
proof (rule toy_leaf_hash.h_leaf_collision_to_sponge_collision)
  show "1 \<le> length [1 :: int, 5, 0]" and "length [1 :: int, 5, 0] \<le> 31"
    and "1 \<le> length [1 :: int, 3, 2]" and "length [1 :: int, 3, 2] \<le> 31"
    by simp_all
  show "[1 :: int, 5, 0] \<noteq> [1, 3, 2]" by simp
  show "sum_list (leaf_fold [1 :: int, 5, 0] 31) = sum_list (leaf_fold [1 :: int, 3, 2] 31)"
    by (simp add: leaf_fold_def sum_list_replicate)
qed

end
