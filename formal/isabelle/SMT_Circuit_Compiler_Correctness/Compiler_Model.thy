(*
  Title:   Compiler_Model.thy
  Session: SMT_Circuit_Compiler_Correctness (SMT-specific layer)

  Deep-embedded MODEL of the SMT verification-circuit compiler.

  The model `compile` constructs an actual `layered_circuit` value at the
  SEMANTIC-BLOCK level: one residual output layer generated from an
  explicit constraint-descriptor list, stacked on an evaluation stack that
  computes the hash values and key-bit multiplexers.  The constraint SET
  mirrors the frozen core compiler (compile.rs) exactly:

    - leaf-hash binding        h_leaf(leaf_pre) = acc_0        (8-lane, F_LEAF_RES)
    - d compression levels     h_node(mux_l) = acc_{l+1}       (key-bit mux, F_NODE_RES)
    - root binding             acc_d = root                    (F_ROOT_RES)
    - value_digest binding     acc_0 = vd  (read-only ops)     (F_VD_RES)
                               acc2_0 = vd (Update, NEW leaf)
    - key-bit booleanity       s*(s-1) = 0
    - NonMembership tag        tag*(tag-2) = 0                 (domain separation)
    - Update second path       new-leaf chain to root2, same siblings/key bits

  Layer/width layout is NOT mirrored (an explicit modeling freedom: the
  Rust builder's gate-layout optimization is a refinement-map concern);
  what IS mirrored is the constraint set and the mux arithmetic
  (left = acc + s*(sib - acc), right = sib + s*(acc - sib), build_mux).

  HASH SUB-CIRCUIT BOUNDARY: the layers
  computing the in-circuit hashes are an ABSTRACT locale parameter
  (`stack`), constrained only by the generator-correctness specification
  `stack_spec`: evaluating those layers on the input vector yields the
  vector of hash values / mux images / carried inputs described by
  `eval_vec`.  Poseidon2's gate-level arithmetization correctness is NOT
  proven here - it is pinned by code-level basis-probe cross-checks
  (compile.rs tests) and stays a blackbox behind this interface.  No
  collision-resistance assumption appears anywhere (Theorem A is a
  deterministic equivalence).

  Rust refinement map (crate `ssgkr-compiler`):
    op_kind          ~ SmtOpKind
    ro_* / up_* offsets ~ InputLayout (same segment order)
    encode_ro/encode_up ~ build_input_vector (witness.rs)
    acc_list         ~ acc_chain (witness.rs)
    mux_left/mux_right ~ build_mux (compile.rs)
    res_desc/res_gates ~ the residual gates emitted by compile.rs
    compile          ~ compile.rs `compile` (semantic-block level)
*)

theory Compiler_Model
  imports SMT_Semantics
begin

section \<open>Operation kinds\<close>

text \<open>
  Circuit structure depends only on the operation KIND (witness-independent
  compile cache - the Module-3 batching premise).  Rust: \<open>SmtOpKind\<close>.
\<close>

datatype op_kind = KMembership | KNonMembership | KUpdate

fun kind_of :: "'v smt_op \<Rightarrow> op_kind" where
  "kind_of (Membership k v) = KMembership"
| "kind_of (NonMembership k) = KNonMembership"
| "kind_of (Update k old new) = KUpdate"

section \<open>List segment utilities\<close>

definition seg :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "seg a w xs = take w (drop a xs)"

lemma length_seg: "a + w \<le> length xs \<Longrightarrow> length (seg a w xs) = w"
  by (simp add: seg_def)

lemma seg_nth: "i < w \<Longrightarrow> a + w \<le> length xs \<Longrightarrow> seg a w xs ! i = xs ! (a + i)"
  by (simp add: seg_def add.commute)

lemma seg_append_in: "a + w \<le> length xs \<Longrightarrow> seg a w (xs @ ys) = seg a w xs"
  by (simp add: seg_def)

text \<open>Indexing a concatenation of uniform-length blocks.\<close>

lemma concat_map_uniform_length:
  assumes "\<And>j. j < n \<Longrightarrow> length (f j) = W"
  shows "length (concat (map f [0 ..< n])) = n * W"
  using assms by (induction n) (auto simp: length_concat)

lemma concat_map_uniform_nth:
  assumes uni: "\<And>j. j < n \<Longrightarrow> length (f j) = W"
      and l: "l < n" and i: "i < W"
  shows "concat (map f [0 ..< n]) ! (l * W + i) = f l ! i"
proof -
  have split: "[0 ..< n] = [0 ..< l] @ l # [Suc l ..< n]"
  proof -
    from l have n_decomp: "n = l + Suc (n - Suc l)" by arith
    have "[0 ..< l + Suc (n - Suc l)] = [0 ..< l] @ [l ..< l + Suc (n - Suc l)]"
      by (rule upt_add_eq_append) simp
    moreover have "[l ..< l + Suc (n - Suc l)] = l # [Suc l ..< l + Suc (n - Suc l)]"
      by (rule upt_conv_Cons) simp
    ultimately have "[0 ..< l + Suc (n - Suc l)]
                   = [0 ..< l] @ l # [Suc l ..< l + Suc (n - Suc l)]" by simp
    then show ?thesis using n_decomp by simp
  qed
  have len_pre: "length (concat (map f [0 ..< l])) = l * W"
    using uni l by (intro concat_map_uniform_length) auto
  have "concat (map f [0 ..< n]) = concat (map f [0 ..< l]) @ f l @ concat (map f [Suc l ..< n])"
    by (simp add: split)
  then show ?thesis
    using len_pre i uni[OF l]
    by (simp add: nth_append)
qed

section \<open>Constraint descriptors and the residual output layer\<close>

text \<open>
  A residual constraint over the layer below (the evaluation-stack top):
  \<open>RDiff a b\<close> vanishes iff wire a equals wire b; \<open>RBool a\<close> is the key-bit
  booleanity residual s*(s-1); \<open>RTag a\<close> is the NonMembership tag residual
  tag*(tag-2) (roots exactly {0,2} in an integral domain).  Rust: the
  residual nodes pushed to `outputs` in compile.rs.
\<close>

datatype res_desc =
    RDiff nat nat
  | RBool nat
  | RTag nat

fun res_gates :: "nat \<Rightarrow> res_desc \<Rightarrow> 'f::comm_ring_1 gate list" where
  "res_gates z (RDiff a b) =
     [ \<lparr> g_kind = GLin, g_out = z, g_in1 = a, g_in2 = a, g_coeff = 1 \<rparr>,
       \<lparr> g_kind = GLin, g_out = z, g_in1 = b, g_in2 = b, g_coeff = - 1 \<rparr> ]"
| "res_gates z (RBool a) =
     [ \<lparr> g_kind = GMul, g_out = z, g_in1 = a, g_in2 = a, g_coeff = 1 \<rparr>,
       \<lparr> g_kind = GLin, g_out = z, g_in1 = a, g_in2 = a, g_coeff = - 1 \<rparr> ]"
| "res_gates z (RTag a) =
     [ \<lparr> g_kind = GMul, g_out = z, g_in1 = a, g_in2 = a, g_coeff = 1 \<rparr>,
       \<lparr> g_kind = GLin, g_out = z, g_in1 = a, g_in2 = a, g_coeff = - 2 \<rparr> ]"

fun res_sem :: "'f::comm_ring_1 list \<Rightarrow> res_desc \<Rightarrow> 'f" where
  "res_sem below (RDiff a b) = below ! a - below ! b"
| "res_sem below (RBool a) = below ! a * below ! a - below ! a"
| "res_sem below (RTag a) = below ! a * below ! a - 2 * below ! a"

text \<open>
  The residual layer: one output wire per descriptor, generated by
  enumeration.  Width is padded to the next power of two implicitly by
  taking \<open>layer_width_bits = length ds\<close> (\<open>n < 2 ^ n\<close>), a modeling freedom -
  padding wires carry no gates and no constants, hence evaluate to 0 and
  never obstruct acceptance.
\<close>

definition mk_res_layer :: "res_desc list \<Rightarrow> 'f::comm_ring_1 layer" where
  "mk_res_layer ds =
     \<lparr> layer_width_bits = length ds,
       layer_gates = concat (map (\<lambda>(z, rd). res_gates z rd) (List.enumerate 0 ds)),
       layer_consts = [] \<rparr>"

subsection \<open>Evaluation of the residual layer\<close>

lemma res_gates_out: "g \<in> set (res_gates z rd) \<Longrightarrow> g_out g = z"
  by (cases rd) auto

lemma filter_res_gates_same:
  "filter (\<lambda>g. g_out g = z) (res_gates z rd) = res_gates z rd"
  by (cases rd) auto

lemma filter_res_gates_other:
  "k \<noteq> z \<Longrightarrow> filter (\<lambda>g. g_out g = z) (res_gates k rd) = []"
  by (cases rd) auto

lemma filter_enumerate_res_gates_miss:
  assumes "z < n \<or> n + length ds \<le> z"
  shows "filter (\<lambda>g. g_out g = z)
           (concat (map (\<lambda>(k, rd). res_gates k rd) (List.enumerate n ds))) = []"
  using assms
proof (induction ds arbitrary: n)
  case Nil then show ?case by simp
next
  case (Cons rd ds)
  then have "z \<noteq> n" and rest: "z < Suc n \<or> Suc n + length ds \<le> z" by auto
  with Cons.IH[OF rest] show ?case
    by (simp add: filter_res_gates_other)
qed

lemma filter_enumerate_res_gates:
  assumes "n \<le> z" "z < n + length ds"
  shows "filter (\<lambda>g. g_out g = z)
           (concat (map (\<lambda>(k, rd). res_gates k rd) (List.enumerate n ds)))
         = (res_gates z (ds ! (z - n)) :: 'f::comm_ring_1 gate list)"
  using assms
proof (induction ds arbitrary: n)
  case Nil then show ?case by simp
next
  case (Cons rd ds)
  show ?case
  proof (cases "n = z")
    case True
    have "filter (\<lambda>g. g_out g = z)
            (concat (map (\<lambda>(k, rd). res_gates k rd) (List.enumerate (Suc n) ds))) = []"
      using True by (intro filter_enumerate_res_gates_miss) simp
    with True show ?thesis
      by (simp add: filter_res_gates_same)
  next
    case False
    with Cons.prems have le: "Suc n \<le> z" and lt: "z < Suc n + length ds" by auto
    have ih: "filter (\<lambda>g. g_out g = z)
        (concat (map (\<lambda>(k, rd). res_gates k rd) (List.enumerate (Suc n) ds)))
      = (res_gates z (ds ! (z - Suc n)) :: 'f gate list)"
      by (rule Cons.IH[OF le lt])
    have idx: "(rd # ds) ! (z - n) = ds ! (z - Suc n)"
      using le by (simp add: Suc_diff_le nth_Cons')
    from False show ?thesis
      by (simp add: filter_res_gates_other ih idx)
  qed
qed

lemma filter_enumerate_res_gates_beyond:
  assumes "n + length ds \<le> z"
  shows "filter (\<lambda>g. g_out g = z)
           (concat (map (\<lambda>(k, rd). res_gates k rd) (List.enumerate n ds))) = []"
  using assms by (intro filter_enumerate_res_gates_miss) simp

lemma res_gates_contrib_sum:
  "sum_list (map (\<lambda>g. gate_contrib g below) (res_gates z rd)) = res_sem below rd"
  by (cases rd) (simp_all add: gate_contrib_def algebra_simps)

lemma mk_res_layer_width: "layer_width (mk_res_layer ds) = 2 ^ length ds"
  by (simp add: mk_res_layer_def layer_width_def)

lemma res_index_width:
  "z < length ds \<Longrightarrow> z < layer_width (mk_res_layer ds)"
  unfolding mk_res_layer_width by (meson less_exp less_trans)

lemma mk_res_layer_gates:
  "layer_gates (mk_res_layer ds)
   = concat (map (\<lambda>(z, rd). res_gates z rd) (List.enumerate 0 ds))"
  by (simp add: mk_res_layer_def)

lemma mk_res_layer_consts: "const_at (mk_res_layer ds) z = 0"
  by (simp add: mk_res_layer_def const_at_def)

lemma mk_res_layer_eval_in:
  assumes z: "z < length ds"
  shows "layer_eval (mk_res_layer ds) below ! z = res_sem below (ds ! z)"
proof -
  have flt: "filter (\<lambda>g. g_out g = z) (layer_gates (mk_res_layer ds))
             = res_gates z (ds ! z)"
    using filter_enumerate_res_gates[of 0 z ds] z
    by (simp add: mk_res_layer_gates)
  show ?thesis
    using layer_eval_nth[OF res_index_width[OF z]]
    by (simp add: flt mk_res_layer_consts res_gates_contrib_sum)
qed

lemma mk_res_layer_eval_pad:
  fixes below :: "'f::comm_ring_1 list"
  assumes ge: "length ds \<le> z"
      and zw: "z < layer_width (mk_res_layer ds :: 'f layer)"
  shows "layer_eval (mk_res_layer ds) below ! z = 0"
proof -
  have flt: "filter (\<lambda>g. g_out g = z) (layer_gates (mk_res_layer ds :: 'f layer)) = []"
    using filter_enumerate_res_gates_beyond[of 0 ds z] ge
    by (simp add: mk_res_layer_gates)
  show ?thesis
    by (simp add: layer_eval_nth[OF zw] flt mk_res_layer_consts)
qed

text \<open>Acceptance of a residual layer over a fixed below-vector.\<close>

lemma mk_res_layer_accept_iff:
  "(\<forall>v \<in> set (layer_eval (mk_res_layer ds) below). v = 0)
   \<longleftrightarrow> (\<forall>rd \<in> set ds. res_sem below rd = 0)"
proof
  assume L: "\<forall>v \<in> set (layer_eval (mk_res_layer ds) below). v = 0"
  show "\<forall>rd \<in> set ds. res_sem below rd = 0"
  proof
    fix rd assume "rd \<in> set ds"
    then obtain z where z: "z < length ds" "ds ! z = rd"
      by (meson in_set_conv_nth)
    have "layer_eval (mk_res_layer ds) below ! z
          \<in> set (layer_eval (mk_res_layer ds) below)"
      using res_index_width[OF z(1)] by (intro nth_mem) simp
    then have zero: "layer_eval (mk_res_layer ds) below ! z = 0"
      using L by blast
    show "res_sem below rd = 0"
      using zero z(2) by (simp add: mk_res_layer_eval_in[OF z(1)])
  qed
next
  assume R: "\<forall>rd \<in> set ds. res_sem below rd = 0"
  show "\<forall>v \<in> set (layer_eval (mk_res_layer ds) below). v = 0"
  proof
    fix v assume "v \<in> set (layer_eval (mk_res_layer ds) below)"
    then obtain z where zl: "z < length (layer_eval (mk_res_layer ds) below)"
                    and v: "v = layer_eval (mk_res_layer ds) below ! z"
      unfolding in_set_conv_nth by blast
    show "v = 0"
    proof (cases "z < length ds")
      case True
      have ev: "layer_eval (mk_res_layer ds) below ! z = res_sem below (ds ! z)"
        by (rule mk_res_layer_eval_in[OF True])
      have "res_sem below (ds ! z) = 0"
        using R nth_mem[OF True] by blast
      with ev v show ?thesis by simp
    next
      case False
      then have "layer_eval (mk_res_layer ds) below ! z = 0"
        using zl by (simp add: mk_res_layer_eval_pad)
      with v show ?thesis by simp
    qed
  qed
qed

section \<open>Key-bit multiplexer (Rust: build\_mux)\<close>

text \<open>
  \<open>left[i] = acc[i] + s * (sib[i] - acc[i])\<close>,
  \<open>right[i] = sib[i] + s * (acc[i] - sib[i])\<close>: selector 0 keeps
  (acc, sib), selector 1 swaps to (sib, acc) - literally the compress
  order of \<open>MerklePath::compute_root\<close> (key low bit first).
\<close>

definition mux_left :: "'f::comm_ring_1 \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f list" where
  "mux_left s as ss = map2 (\<lambda>a sb. a + s * (sb - a)) as ss"

definition mux_right :: "'f::comm_ring_1 \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f list" where
  "mux_right s as ss = map2 (\<lambda>a sb. sb + s * (a - sb)) as ss"

lemma mux_zero:
  assumes "length as = length ss"
  shows "mux_left 0 as ss = as" and "mux_right 0 as ss = ss"
  using assms
  unfolding mux_left_def mux_right_def
  by (induction as ss rule: list_induct2) auto

lemma mux_one:
  assumes "length as = length ss"
  shows "mux_left 1 as ss = ss" and "mux_right 1 as ss = as"
  using assms
  unfolding mux_left_def mux_right_def
  by (induction as ss rule: list_induct2) auto

section \<open>Kind tags and key bits\<close>

text \<open>Leaf-encoding tag lane (domain separation): 0/1/2.\<close>

fun leaf_tag_val :: "'v leaf_state \<Rightarrow> 'f::comm_ring_1" where
  "leaf_tag_val Empty = 0"
| "leaf_tag_val (Occupied v) = 1"
| "leaf_tag_val Tombstone = 2"

text \<open>Key bit \<open>l\<close> as a field element (Rust: \<open>(key.0 >> l) & 1\<close>).\<close>

definition kbit :: "nat \<Rightarrow> nat \<Rightarrow> 'f::comm_ring_1" where
  "kbit key l = of_nat ((key div 2 ^ l) mod 2)"

lemma kbit_cases: "kbit key l = 0 \<or> kbit key l = 1"
proof -
  have "(key div 2 ^ l) mod 2 = 0 \<or> (key div 2 ^ l) mod 2 = 1" by auto
  then show ?thesis by (auto simp: kbit_def)
qed

lemma kbit_bool: "kbit key l * (kbit key l - 1) = 0"
proof -
  have "(key div 2 ^ l) mod 2 = 0 \<or> (key div 2 ^ l) mod 2 = 1" by auto
  then show ?thesis unfolding kbit_def by (elim disjE) simp_all
qed

section \<open>Zero padding\<close>

definition pad_to :: "nat \<Rightarrow> 'f::comm_ring_1 list \<Rightarrow> 'f list" where
  "pad_to n xs = xs @ replicate (n - length xs) 0"

lemma length_pad_to: "length xs \<le> n \<Longrightarrow> length (pad_to n xs) = n"
  by (simp add: pad_to_def)

lemma pad_to_nth: "i < length xs \<Longrightarrow> pad_to n xs ! i = xs ! i"
  by (simp add: pad_to_def nth_append)

lemma seg_pad_to: "a + w \<le> length xs \<Longrightarrow> seg a w (pad_to n xs) = seg a w xs"
  by (simp add: pad_to_def seg_append_in)

section \<open>The compiler model locale (representation layer)\<close>

text \<open>
  Extends the frozen SMT semantics with the field-level REPRESENTATION of
  digests and leaf pre-images the circuit operates on:

    \<open>digest_repr\<close> ~ a digest as W field lanes (Rust: Digest<BaseField>, W=8);
                  injective - two digests are equal iff their lane vectors
                  are (the wire-level equality tests decide digest equality)
    \<open>leaf_repr\<close>   ~ the FIXED lossless leaf pre-image (Rust: \<open>leaf_fold\<close> of the
                  leaf encoding, L = \<open>leaf_pre_width\<close> lanes); lane 0 carries
                  the encoding tag (domain separation).  Injectivity
                  of \<open>leaf_fold\<close> is lemma (b) territory (\<open>Leaf_Fold\<close>.thy) and
                  is NOT consumed here - Theorem A only needs the tag lane.
    hl / hn     ~ the lane-level hash maps the in-circuit hash sub-circuits
                  compute (Rust: \<open>hash_leaf_pre\<close> / compress gadgets); their
                  agreement with the abstract \<open>h_leaf\<close> / \<open>h_node\<close> is the
                  generator-correctness boundary (black-box hash layers).

  No collision resistance and no injectivity of \<open>h_leaf\<close>/\<open>h_node\<close> is assumed
  (Theorem A is a deterministic equivalence).
\<close>

locale compiler_model_base = smt_semantics params h_leaf h_node
  for params :: smt_params
  and h_leaf :: "'v leaf_state \<Rightarrow> 'd"
  and h_node :: "'d \<Rightarrow> 'd \<Rightarrow> 'd" +
  fixes W :: nat and L :: nat
    and digest_repr :: "'d \<Rightarrow> 'f::idom list"
    and leaf_repr :: "'v leaf_state \<Rightarrow> 'f list"
    and hl :: "'f list \<Rightarrow> 'f list"
    and hn :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list"
  assumes L_pos: "0 < L"
    and digest_len [simp]: "\<And>x. length (digest_repr x) = W"
    and digest_inj: "\<And>x y. digest_repr x = digest_repr y \<Longrightarrow> x = y"
    and leaf_len [simp]: "\<And>lf. length (leaf_repr lf) = L"
    and leaf_tag: "\<And>lf. leaf_repr lf ! 0 = leaf_tag_val lf"
    and hl_len [simp]: "\<And>xs. length (hl xs) = W"
    and hn_len [simp]: "\<And>a b. length (hn a b) = W"
    and hl_correct: "\<And>lf. hl (leaf_repr lf) = digest_repr (h_leaf lf)"
    and hn_correct: "\<And>a b. hn (digest_repr a) (digest_repr b) = digest_repr (h_node a b)"
begin

abbreviation dd :: nat where "dd \<equiv> depth params"

subsection \<open>Input-vector layout (Rust: InputLayout, same segment order)\<close>

text \<open>Read-only ops (Membership / NonMembership).\<close>

definition ro_lp :: nat where "ro_lp = 0"
definition ro_acc :: "nat \<Rightarrow> nat" where "ro_acc l = L + W * l"
definition ro_sib :: "nat \<Rightarrow> nat" where "ro_sib l = L + W * (dd + 1) + W * l"
definition ro_kb :: "nat \<Rightarrow> nat" where "ro_kb l = L + W * (2 * dd + 1) + l"
definition ro_root :: nat where "ro_root = L + W * (2 * dd + 1) + dd"
definition ro_vd :: nat where "ro_vd = ro_root + W"
definition ro_width :: nat where "ro_width = ro_vd + W"

text \<open>Update (two leaf pre-images, two accumulator chains, two roots).\<close>

definition up_lp :: nat where "up_lp = 0"
definition up_lp2 :: nat where "up_lp2 = L"
definition up_acc :: "nat \<Rightarrow> nat" where "up_acc l = 2 * L + W * l"
definition up_acc2 :: "nat \<Rightarrow> nat" where "up_acc2 l = 2 * L + W * (dd + 1) + W * l"
definition up_sib :: "nat \<Rightarrow> nat" where "up_sib l = 2 * L + 2 * W * (dd + 1) + W * l"
definition up_kb :: "nat \<Rightarrow> nat" where "up_kb l = 2 * L + W * (3 * dd + 2) + l"
definition up_root :: nat where "up_root = 2 * L + W * (3 * dd + 2) + dd"
definition up_root2 :: nat where "up_root2 = up_root + W"
definition up_vd :: nat where "up_vd = up_root2 + W"
definition up_width :: nat where "up_width = up_vd + W"

text \<open>
  Input vectors are zero-padded to a power of two.  The model takes
  \<open>input_width_bits = width\<close> itself (\<open>n < 2 ^ n\<close>) - a deliberately
  generous padding; wire-width economy is a refinement concern, not semantics.
\<close>

fun in_width :: "op_kind \<Rightarrow> nat" where
  "in_width KMembership = ro_width"
| "in_width KNonMembership = ro_width"
| "in_width KUpdate = up_width"

definition iwb :: "op_kind \<Rightarrow> nat" where "iwb k = in_width k"

definition ivlen :: "op_kind \<Rightarrow> nat" where "ivlen k = 2 ^ iwb k"

lemma in_width_le_ivlen: "in_width k \<le> ivlen k"
  by (simp add: ivlen_def iwb_def less_imp_le[OF less_exp])

subsection \<open>Evaluation-stack output specification\<close>

text \<open>
  \<open>ev_ro xs\<close> / \<open>ev_up xs\<close>: the vector the hash/mux evaluation stack must
  produce on top of input vector \<open>xs\<close> - the in-circuit hash values, the
  mux images feeding them, and the carried inputs the residual layer
  compares against.  The mux arithmetic is EXPLICIT here (the key-bit mux
  is a soundness-critical constraint structure); only the hash maps
  hl/hn are abstract.

  PADDING (non-vacuity fix): \<open>layer_eval\<close> always produces a vector
  of power-of-two length (\<open>layer_width = 2 ^ layer_width_bits\<close>), so the
  stack specification target must itself have power-of-two length or the
  \<open>stack_spec\<close> assumptions would be UNSATISFIABLE - the core (unpadded)
  lengths of the two vectors are locked in the open interval
  \<open>(len_ro, 2 * len_ro)\<close> relative to each other, so no width parameters
  can make both powers of two.  The specification therefore zero-pads the
  core vector to width \<open>2 ^ core-length\<close> (the same \<open>n < 2 ^ n\<close> modeling
  freedom as \<open>iwb\<close> and \<open>mk_res_layer\<close>), mirroring the Rust builder whose
  layers are power-of-two wide with unused wires at zero.
\<close>

definition ro_mxl :: "'f list \<Rightarrow> nat \<Rightarrow> 'f list" where
  "ro_mxl xs l = mux_left (xs ! ro_kb l) (seg (ro_acc l) W xs) (seg (ro_sib l) W xs)"

definition ro_mxr :: "'f list \<Rightarrow> nat \<Rightarrow> 'f list" where
  "ro_mxr xs l = mux_right (xs ! ro_kb l) (seg (ro_acc l) W xs) (seg (ro_sib l) W xs)"

definition ev_ro_core :: "'f list \<Rightarrow> 'f list" where
  "ev_ro_core xs =
     hl (seg ro_lp L xs)
   @ concat (map (\<lambda>l. hn (ro_mxl xs l) (ro_mxr xs l)) [0 ..< dd])
   @ concat (map (\<lambda>l. seg (ro_acc l) W xs) [0 ..< Suc dd])
   @ map (\<lambda>l. xs ! ro_kb l) [0 ..< dd]
   @ seg ro_root W xs
   @ seg ro_vd W xs
   @ [xs ! ro_lp]"

definition ev_hl :: nat where "ev_hl = 0"
definition ev_hn :: "nat \<Rightarrow> nat" where "ev_hn l = W + W * l"
definition ev_acc :: "nat \<Rightarrow> nat" where "ev_acc l = W * (dd + 1) + W * l"
definition ev_kb :: "nat \<Rightarrow> nat" where "ev_kb l = W * (2 * dd + 2) + l"
definition ev_root :: nat where "ev_root = W * (2 * dd + 2) + dd"
definition ev_vd :: nat where "ev_vd = ev_root + W"
definition ev_tag :: nat where "ev_tag = ev_vd + W"

definition ev_ro_len :: nat where "ev_ro_len = ev_tag + 1"

definition ev_ro :: "'f list \<Rightarrow> 'f list" where
  "ev_ro xs = pad_to (2 ^ ev_ro_len) (ev_ro_core xs)"

definition up_mxl :: "'f list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'f list" where
  "up_mxl xs acc l = mux_left (xs ! up_kb l) (seg (acc l) W xs) (seg (up_sib l) W xs)"

definition up_mxr :: "'f list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'f list" where
  "up_mxr xs acc l = mux_right (xs ! up_kb l) (seg (acc l) W xs) (seg (up_sib l) W xs)"

definition ev_up_core :: "'f list \<Rightarrow> 'f list" where
  "ev_up_core xs =
     hl (seg up_lp L xs)
   @ hl (seg up_lp2 L xs)
   @ concat (map (\<lambda>l. hn (up_mxl xs up_acc l) (up_mxr xs up_acc l)) [0 ..< dd])
   @ concat (map (\<lambda>l. hn (up_mxl xs up_acc2 l) (up_mxr xs up_acc2 l)) [0 ..< dd])
   @ concat (map (\<lambda>l. seg (up_acc l) W xs) [0 ..< Suc dd])
   @ concat (map (\<lambda>l. seg (up_acc2 l) W xs) [0 ..< Suc dd])
   @ map (\<lambda>l. xs ! up_kb l) [0 ..< dd]
   @ seg up_root W xs
   @ seg up_root2 W xs
   @ seg up_vd W xs"

definition ev2_hl :: nat where "ev2_hl = 0"
definition ev2_hl2 :: nat where "ev2_hl2 = W"
definition ev2_hn :: "nat \<Rightarrow> nat" where "ev2_hn l = 2 * W + W * l"
definition ev2_hn2 :: "nat \<Rightarrow> nat" where "ev2_hn2 l = 2 * W + W * dd + W * l"
definition ev2_acc :: "nat \<Rightarrow> nat" where "ev2_acc l = W * (2 * dd + 2) + W * l"
definition ev2_acc2 :: "nat \<Rightarrow> nat" where "ev2_acc2 l = W * (3 * dd + 3) + W * l"
definition ev2_kb :: "nat \<Rightarrow> nat" where "ev2_kb l = W * (4 * dd + 4) + l"
definition ev2_root :: nat where "ev2_root = W * (4 * dd + 4) + dd"
definition ev2_root2 :: nat where "ev2_root2 = ev2_root + W"
definition ev2_vd :: nat where "ev2_vd = ev2_root2 + W"

definition ev_up_len :: nat where "ev_up_len = ev2_vd + W"

definition ev_up :: "'f list \<Rightarrow> 'f list" where
  "ev_up xs = pad_to (2 ^ ev_up_len) (ev_up_core xs)"

subsection \<open>Residual constraint descriptors (the constraint SET of compile.rs)\<close>

text \<open>
  Read-only ops: leaf-hash binding, dd compression transitions, root
  binding, value-digest binding (\<open>acc_0\<close> = vd: the leaf being authenticated),
  key-bit booleanity, and - NonMembership only - the tag residual.
\<close>

definition descs_ro :: "op_kind \<Rightarrow> res_desc list" where
  "descs_ro k =
     map (\<lambda>i. RDiff (ev_hl + i) (ev_acc 0 + i)) [0 ..< W]
   @ concat (map (\<lambda>l. map (\<lambda>i. RDiff (ev_hn l + i) (ev_acc (Suc l) + i)) [0 ..< W]) [0 ..< dd])
   @ map (\<lambda>i. RDiff (ev_acc dd + i) (ev_root + i)) [0 ..< W]
   @ map (\<lambda>i. RDiff (ev_acc 0 + i) (ev_vd + i)) [0 ..< W]
   @ map (\<lambda>l. RBool (ev_kb l)) [0 ..< dd]
   @ (if k = KNonMembership then [RTag ev_tag] else [])"

text \<open>
  Update: both paths (old leaf to root, new leaf to root2) over the SAME
  siblings and key bits; \<open>value_digest\<close> binds the NEW leaf (S-6): \<open>acc2_0\<close> = vd.
\<close>

definition descs_up :: "res_desc list" where
  "descs_up =
     map (\<lambda>i. RDiff (ev2_hl + i) (ev2_acc 0 + i)) [0 ..< W]
   @ map (\<lambda>i. RDiff (ev2_hl2 + i) (ev2_acc2 0 + i)) [0 ..< W]
   @ concat (map (\<lambda>l. map (\<lambda>i. RDiff (ev2_hn l + i) (ev2_acc (Suc l) + i)) [0 ..< W]) [0 ..< dd])
   @ concat (map (\<lambda>l. map (\<lambda>i. RDiff (ev2_hn2 l + i) (ev2_acc2 (Suc l) + i)) [0 ..< W]) [0 ..< dd])
   @ map (\<lambda>i. RDiff (ev2_acc dd + i) (ev2_root + i)) [0 ..< W]
   @ map (\<lambda>i. RDiff (ev2_acc2 dd + i) (ev2_root2 + i)) [0 ..< W]
   @ map (\<lambda>i. RDiff (ev2_acc2 0 + i) (ev2_vd + i)) [0 ..< W]
   @ map (\<lambda>l. RBool (ev2_kb l)) [0 ..< dd]"

fun descs :: "op_kind \<Rightarrow> res_desc list" where
  "descs KUpdate = descs_up"
| "descs k = descs_ro k"

subsection \<open>Constraint conjunction (the A-i target semantics)\<close>

definition cons_ro :: "op_kind \<Rightarrow> 'f list \<Rightarrow> bool" where
  "cons_ro k xs \<longleftrightarrow>
     hl (seg ro_lp L xs) = seg (ro_acc 0) W xs
   \<and> (\<forall>l<dd. hn (ro_mxl xs l) (ro_mxr xs l) = seg (ro_acc (Suc l)) W xs)
   \<and> seg (ro_acc dd) W xs = seg ro_root W xs
   \<and> seg (ro_acc 0) W xs = seg ro_vd W xs
   \<and> (\<forall>l<dd. xs ! ro_kb l * (xs ! ro_kb l - 1) = 0)
   \<and> (k = KNonMembership \<longrightarrow> xs ! ro_lp * (xs ! ro_lp - 2) = 0)"

definition cons_up :: "'f list \<Rightarrow> bool" where
  "cons_up xs \<longleftrightarrow>
     hl (seg up_lp L xs) = seg (up_acc 0) W xs
   \<and> hl (seg up_lp2 L xs) = seg (up_acc2 0) W xs
   \<and> (\<forall>l<dd. hn (up_mxl xs up_acc l) (up_mxr xs up_acc l) = seg (up_acc (Suc l)) W xs)
   \<and> (\<forall>l<dd. hn (up_mxl xs up_acc2 l) (up_mxr xs up_acc2 l) = seg (up_acc2 (Suc l)) W xs)
   \<and> seg (up_acc dd) W xs = seg up_root W xs
   \<and> seg (up_acc2 dd) W xs = seg up_root2 W xs
   \<and> seg (up_acc2 0) W xs = seg up_vd W xs
   \<and> (\<forall>l<dd. xs ! up_kb l * (xs ! up_kb l - 1) = 0)"

subsection \<open>Witness encoding (Rust: build\_input\_vector)\<close>

text \<open>
  The honest accumulator chain along one path: \<open>acc_0\<close> is the leaf digest,
  \<open>acc_{l+1}\<close> compresses \<open>acc_l\<close> with sibling \<open>l\<close> in key-bit order -
  exactly \<open>MerklePath::compute_root\<close>'s recursion retaining intermediates
  (Rust: \<open>acc_chain\<close>, witness.rs).
\<close>

fun acc_list :: "'d \<Rightarrow> nat \<Rightarrow> 'd list \<Rightarrow> 'd list" where
  "acc_list a key [] = [a]"
| "acc_list a key (s # ss) =
     a # acc_list (if key mod 2 = 0 then h_node a s else h_node s a) (key div 2) ss"

lemma length_acc_list [simp]: "length (acc_list a key ss) = Suc (length ss)"
  by (induction ss arbitrary: a key) auto

lemma acc_list_0 [simp]: "acc_list a key ss ! 0 = a"
  by (cases ss) auto

lemma acc_list_ne [simp]: "acc_list a key ss \<noteq> []"
  by (cases ss) auto

lemma acc_list_last: "last (acc_list a key ss) = path_root a key ss"
  by (induction a key ss rule: acc_list.induct) auto

lemma acc_list_step:
  assumes "l < length ss"
  shows "acc_list a key ss ! Suc l =
           (if (key div 2 ^ l) mod 2 = 0
            then h_node (acc_list a key ss ! l) (ss ! l)
            else h_node (ss ! l) (acc_list a key ss ! l))"
  using assms
proof (induction ss arbitrary: a key l)
  case Nil then show ?case by simp
next
  case (Cons s ss)
  show ?case
  proof (cases l)
    case 0 then show ?thesis by simp
  next
    case (Suc l')
    with Cons.prems have "l' < length ss" by simp
    from Cons.IH[OF this] Suc show ?thesis
      by (simp add: div_mult2_eq [symmetric] mult.commute)
  qed
qed

text \<open>
  Read-only input encoding: leaf pre-image, honest accumulator chain,
  siblings, key bits, public root and value digest - the segment order of
  \<open>InputLayout\<close> - zero-padded to the power-of-two input width.
\<close>

definition enc_ro_core :: "'v leaf_state \<Rightarrow> nat \<Rightarrow> 'd list \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'f list" where
  "enc_ro_core leaf key sibs root vd =
     leaf_repr leaf
   @ concat (map (\<lambda>l. digest_repr (acc_list (h_leaf leaf) key sibs ! l)) [0 ..< Suc dd])
   @ concat (map (\<lambda>l. digest_repr (sibs ! l)) [0 ..< dd])
   @ map (kbit key) [0 ..< dd]
   @ digest_repr root
   @ digest_repr vd"

definition enc_ro :: "op_kind \<Rightarrow> 'v leaf_state \<Rightarrow> nat \<Rightarrow> 'd list \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'f list" where
  "enc_ro k leaf key sibs root vd = pad_to (ivlen k) (enc_ro_core leaf key sibs root vd)"

text \<open>
  Update input encoding.  The primary path carries the operation's OLD
  leaf, the second path the NEW leaf, over the same siblings and key bits
  (Rust: \<open>build_input_vector\<close> ignores the witness leaf for Update and uses
  the operation's old leaf - mirrored literally here; the agreement of the
  witness leaf with the old leaf is a well-formedness premise of
  Theorem A, matching \<open>smt_valid's\<close> \<open>leaf = old\<close> clause).
\<close>

definition enc_up_core :: "'v leaf_state \<Rightarrow> 'v leaf_state \<Rightarrow> nat \<Rightarrow> 'd list \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'f list" where
  "enc_up_core old new key sibs root root' vd =
     leaf_repr old
   @ leaf_repr new
   @ concat (map (\<lambda>l. digest_repr (acc_list (h_leaf old) key sibs ! l)) [0 ..< Suc dd])
   @ concat (map (\<lambda>l. digest_repr (acc_list (h_leaf new) key sibs ! l)) [0 ..< Suc dd])
   @ concat (map (\<lambda>l. digest_repr (sibs ! l)) [0 ..< dd])
   @ map (kbit key) [0 ..< dd]
   @ digest_repr root
   @ digest_repr root'
   @ digest_repr vd"

definition enc_up :: "'v leaf_state \<Rightarrow> 'v leaf_state \<Rightarrow> nat \<Rightarrow> 'd list \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'f list" where
  "enc_up old new key sibs root root' vd =
     pad_to (ivlen KUpdate) (enc_up_core old new key sibs root root' vd)"

text \<open>The witness encoder of Theorem A (Rust: build\_input\_vector).\<close>

definition encode_witness :: "'v smt_op \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> ('v leaf_state \<times> 'd list) \<Rightarrow> 'f list" where
  "encode_witness op root root' vd w = (case op of
     Membership k v \<Rightarrow> enc_ro KMembership (fst w) k (snd w) root vd
   | NonMembership k \<Rightarrow> enc_ro KNonMembership (fst w) k (snd w) root vd
   | Update k old new \<Rightarrow> enc_up old new k (snd w) root root' vd)"

end

section \<open>The full compiler model (evaluation stack as abstract parameter)\<close>

text \<open>
  HASH SUB-CIRCUIT BOUNDARY: \<open>stack k\<close> is the layer
  list computing the hash values and mux images.  Its only specification
  is generator correctness (\<open>stack_spec_*\<close>): on an input vector of the
  declared width, evaluating the stack yields exactly \<open>ev_ro\<close>/\<open>ev_up\<close>.
  The gate-level Poseidon2 arithmetization inside the stack is NOT proven
  here - it is pinned by the code-level cross-check tests (compile.rs:
  the \<open>poseidon2_*_matches_native\<close> family) and remains a blackbox behind
  this interface.  This is a specification assumption, not a strength
  assumption: no collision resistance, no injectivity of the hashes.
\<close>

locale compiler_model = compiler_model_base params h_leaf h_node W L digest_repr leaf_repr hl hn
  for params :: smt_params
  and h_leaf :: "'v leaf_state \<Rightarrow> 'd"
  and h_node :: "'d \<Rightarrow> 'd \<Rightarrow> 'd"
  and W L :: nat
  and digest_repr :: "'d \<Rightarrow> 'f::idom list"
  and leaf_repr :: "'v leaf_state \<Rightarrow> 'f list"
  and hl hn +
  fixes stack :: "op_kind \<Rightarrow> 'f layer list"
  assumes stack_spec_ro:
    "\<And>k xs. k \<noteq> KUpdate \<Longrightarrow> length xs = ivlen k \<Longrightarrow>
       foldr layer_eval (stack k) xs = ev_ro xs"
    and stack_spec_up:
    "\<And>xs. length xs = ivlen KUpdate \<Longrightarrow>
       foldr layer_eval (stack KUpdate) xs = ev_up xs"
begin

text \<open>
  The model compiler: one residual output layer over the evaluation
  stack.  Rust: \<open>compile\<close> (compile.rs) - the constraint set is identical;
  the layer decomposition differs (a refinement-map freedom).
\<close>

definition compile :: "op_kind \<Rightarrow> 'f layered_circuit" where
  "compile k =
     \<lparr> circ_layers = mk_res_layer (descs k) # stack k,
       input_width_bits = iwb k \<rparr>"

lemma compile_output:
  assumes "length xs = ivlen k"
  shows "circuit_output (compile k) xs
         = layer_eval (mk_res_layer (descs k)) (foldr layer_eval (stack k) xs)"
  by (simp add: circuit_output_foldr compile_def)

end

end
