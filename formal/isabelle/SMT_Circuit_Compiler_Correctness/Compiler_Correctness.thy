(*
  Title:   Compiler_Correctness.thy
  Session: SMT_Circuit_Compiler_Correctness (SMT-specific layer)

  Theorem A - SMT circuit compilation soundness:
    circuit_accept (compile op) (encode_witness ...) <-> smt_valid op ...
  proved in two stages: A-i (acceptance <-> constraint conjunction) and
  A-ii (constraint conjunction <-> smt_valid), per operation kind.
*)

theory Compiler_Correctness
  imports Compiler_Model
begin

context compiler_model_base
begin

section \<open>Slot lemmas for the evaluation-stack specification vector\<close>

lemma ro_seg_bounds:
  "ro_lp + L \<le> ro_width"
  "l \<le> dd \<Longrightarrow> ro_acc l + W \<le> ro_width"
  "l < dd \<Longrightarrow> ro_sib l + W \<le> ro_width"
  "l < dd \<Longrightarrow> ro_kb l < ro_width"
  "ro_root + W \<le> ro_width"
  "ro_vd + W \<le> ro_width"
proof -
  have d1: "W * (2 * dd + 1) = 2 * (W * dd) + W"
    by (simp add: algebra_simps)
  have d2: "W * (dd + 1) = W * dd + W"
    by (simp add: algebra_simps)
  show "ro_lp + L \<le> ro_width"
    unfolding ro_lp_def ro_width_def ro_vd_def ro_root_def by linarith
  show "ro_acc l + W \<le> ro_width" if l: "l \<le> dd"
  proof -
    have m: "W * l \<le> W * dd" using l by (rule mult_le_mono2)
    show ?thesis
      using m d1
      unfolding ro_acc_def ro_width_def ro_vd_def ro_root_def
      by linarith
  qed
  show "ro_sib l + W \<le> ro_width" if l: "l < dd"
  proof -
    have "W * l \<le> W * dd" using less_imp_le[OF l] by (rule mult_le_mono2)
    then have "W * (dd + 1) + W * l \<le> W * (dd + 1) + W * dd"
      by (rule add_left_mono)
    also have "W * (dd + 1) + W * dd = W * (2 * dd + 1)"
      by (simp add: algebra_simps)
    finally have m: "W * (dd + 1) + W * l \<le> W * (2 * dd + 1)" .
    show ?thesis
      using m
      unfolding ro_sib_def ro_width_def ro_vd_def ro_root_def
      by linarith
  qed
  show "ro_kb l < ro_width" if l: "l < dd"
    using l
    unfolding ro_kb_def ro_width_def ro_vd_def ro_root_def
    by linarith
  show "ro_root + W \<le> ro_width"
    unfolding ro_width_def ro_vd_def by linarith
  show "ro_vd + W \<le> ro_width"
    unfolding ro_width_def by linarith
qed

lemma length_seg_ro [simp]:
  assumes "ro_width \<le> length xs"
  shows "length (seg ro_lp L xs) = L"
    and "l \<le> dd \<Longrightarrow> length (seg (ro_acc l) W xs) = W"
    and "l < dd \<Longrightarrow> length (seg (ro_sib l) W xs) = W"
    and "length (seg ro_root W xs) = W"
    and "length (seg ro_vd W xs) = W"
proof -
  show "length (seg ro_lp L xs) = L"
    by (rule length_seg) (rule le_trans[OF ro_seg_bounds(1) assms])
  show "length (seg (ro_acc l) W xs) = W" if l: "l \<le> dd"
    by (rule length_seg) (rule le_trans[OF ro_seg_bounds(2)[OF l] assms])
  show "length (seg (ro_sib l) W xs) = W" if l: "l < dd"
    by (rule length_seg) (rule le_trans[OF ro_seg_bounds(3)[OF l] assms])
  show "length (seg ro_root W xs) = W"
    by (rule length_seg) (rule le_trans[OF ro_seg_bounds(5) assms])
  show "length (seg ro_vd W xs) = W"
    by (rule length_seg) (rule le_trans[OF ro_seg_bounds(6) assms])
qed

text \<open>Uniform block lengths inside \<open>ev_ro\<close>.\<close>

lemma ev_ro_block_lens:
  assumes "ro_width \<le> length xs"
  shows "length (concat (map (\<lambda>l. hn (ro_mxl xs l) (ro_mxr xs l)) [0 ..< dd])) = dd * W"
    and "length (concat (map (\<lambda>l. seg (ro_acc l) W xs) [0 ..< Suc dd])) = Suc dd * W"
  using assms
  by (auto intro!: concat_map_uniform_length simp: length_seg ro_seg_bounds
           intro: order_trans)

text \<open>The core specification vector has exactly the slot-layout length,
  and the padded vector its power-of-two width.\<close>

lemma length_ev_ro_core:
  assumes len: "ro_width \<le> length xs"
  shows "length (ev_ro_core xs) = ev_ro_len"
  using ev_ro_block_lens[OF len] length_seg_ro[OF len]
  by (simp add: ev_ro_core_def ev_ro_len_def ev_tag_def ev_vd_def ev_root_def
                algebra_simps)

lemma ev_ro_core_le_pad: "length (ev_ro_core xs) \<le> 2 ^ ev_ro_len \<Longrightarrow>
  length (ev_ro xs) = 2 ^ ev_ro_len"
  by (simp add: ev_ro_def length_pad_to)

lemma length_ev_ro:
  assumes len: "ro_width \<le> length xs"
  shows "length (ev_ro xs) = 2 ^ ev_ro_len"
  by (rule ev_ro_core_le_pad)
     (simp add: length_ev_ro_core[OF len] less_imp_le[OF less_exp])

lemma block_index_lt: "l < n \<Longrightarrow> i < W \<Longrightarrow> W * l + i < n * W"
proof -
  assume l: "l < n" and i: "i < W"
  have "W * l + i < W * Suc l" using i by simp
  also have "\<dots> \<le> W * n" using Suc_leI[OF l] by (rule mult_le_mono2)
  finally show ?thesis by (simp add: mult.commute)
qed

lemma ev_ro_nth_hl:
  assumes "ro_width \<le> length xs" and i: "i < W"
  shows "ev_ro xs ! (ev_hl + i) = hl (seg ro_lp L xs) ! i"
  using i by (simp add: ev_ro_def pad_to_def ev_ro_core_def ev_hl_def nth_append)

lemma ev_ro_nth_hn:
  assumes len: "ro_width \<le> length xs" and l: "l < dd" and i: "i < W"
  shows "ev_ro xs ! (ev_hn l + i) = hn (ro_mxl xs l) (ro_mxr xs l) ! i"
proof -
  have lt: "W * l + i < dd * W" using block_index_lt l i by simp
  have "ev_ro xs ! (ev_hn l + i)
        = concat (map (\<lambda>j. hn (ro_mxl xs j) (ro_mxr xs j)) [0 ..< dd]) ! (W * l + i)"
    using lt by (simp add: ev_ro_def pad_to_def ev_ro_core_def ev_hn_def nth_append
                           ev_ro_block_lens[OF len] add.assoc)
  also have "\<dots> = hn (ro_mxl xs l) (ro_mxr xs l) ! i"
    using l i by (subst mult.commute[of W l]) (intro concat_map_uniform_nth; simp)
  finally show ?thesis .
qed

lemma ev_ro_nth_acc:
  assumes len: "ro_width \<le> length xs" and l: "l \<le> dd" and i: "i < W"
  shows "ev_ro xs ! (ev_acc l + i) = seg (ro_acc l) W xs ! i"
proof -
  have lt: "W * l + i < Suc dd * W"
    by (rule block_index_lt[OF le_imp_less_Suc[OF l] i])
  have idx: "ev_acc l + i
      = length (hl (seg ro_lp L xs))
        + (length (concat (map (\<lambda>l. hn (ro_mxl xs l) (ro_mxr xs l)) [0 ..< dd]))
        + (W * l + i))"
    using ev_ro_block_lens[OF len] by (simp add: ev_acc_def algebra_simps)
  have lt2: "W * l + i < length (concat (map (\<lambda>l. seg (ro_acc l) W xs) [0 ..< Suc dd]))"
    using ev_ro_block_lens(2)[OF len] lt by simp
  have "ev_ro xs ! (ev_acc l + i)
        = concat (map (\<lambda>j. seg (ro_acc j) W xs) [0 ..< Suc dd]) ! (W * l + i)"
    unfolding ev_ro_def pad_to_def ev_ro_core_def idx append_assoc
    by (simp only: nth_append_length_plus) (simp only: nth_append if_P[OF lt2])
  also have "\<dots> = seg (ro_acc l) W xs ! i"
    using l i len
    by (subst mult.commute[of W l])
       (intro concat_map_uniform_nth; simp add: le_imp_less_Suc)
  finally show ?thesis .
qed

lemma ev_ro_nth_kb:
  assumes len: "ro_width \<le> length xs" and l: "l < dd"
  shows "ev_ro xs ! (ev_kb l) = xs ! ro_kb l"
proof -
  have idx: "ev_kb l
      = length (hl (seg ro_lp L xs))
        + (length (concat (map (\<lambda>l. hn (ro_mxl xs l) (ro_mxr xs l)) [0 ..< dd]))
        + (length (concat (map (\<lambda>l. seg (ro_acc l) W xs) [0 ..< Suc dd]))
        + l))"
    using ev_ro_block_lens[OF len] by (simp add: ev_kb_def algebra_simps)
  show ?thesis
    unfolding ev_ro_def pad_to_def ev_ro_core_def idx append_assoc
    by (simp only: nth_append_length_plus) (simp add: nth_append l nth_upt)
qed

lemma ev_ro_nth_root:
  assumes len: "ro_width \<le> length xs" and i: "i < W"
  shows "ev_ro xs ! (ev_root + i) = seg ro_root W xs ! i"
proof -
  have idx: "ev_root + i
      = length (hl (seg ro_lp L xs))
        + (length (concat (map (\<lambda>l. hn (ro_mxl xs l) (ro_mxr xs l)) [0 ..< dd]))
        + (length (concat (map (\<lambda>l. seg (ro_acc l) W xs) [0 ..< Suc dd]))
        + (length (map (\<lambda>l. xs ! ro_kb l) [0 ..< dd])
        + i)))"
    using ev_ro_block_lens[OF len] by (simp add: ev_root_def algebra_simps)
  show ?thesis
    unfolding ev_ro_def pad_to_def ev_ro_core_def idx append_assoc
    by (simp only: nth_append_length_plus)
       (simp add: nth_append length_seg_ro(4)[OF len] i)
qed

lemma ev_ro_nth_vd:
  assumes len: "ro_width \<le> length xs" and i: "i < W"
  shows "ev_ro xs ! (ev_vd + i) = seg ro_vd W xs ! i"
proof -
  have idx: "ev_vd + i
      = length (hl (seg ro_lp L xs))
        + (length (concat (map (\<lambda>l. hn (ro_mxl xs l) (ro_mxr xs l)) [0 ..< dd]))
        + (length (concat (map (\<lambda>l. seg (ro_acc l) W xs) [0 ..< Suc dd]))
        + (length (map (\<lambda>l. xs ! ro_kb l) [0 ..< dd])
        + (length (seg ro_root W xs)
        + i))))"
    using ev_ro_block_lens[OF len] length_seg_ro(4)[OF len]
    by (simp add: ev_vd_def ev_root_def algebra_simps)
  show ?thesis
    unfolding ev_ro_def pad_to_def ev_ro_core_def idx append_assoc
    by (simp only: nth_append_length_plus)
       (simp add: nth_append length_seg_ro(5)[OF len] i)
qed

lemma ev_ro_nth_tag:
  assumes len: "ro_width \<le> length xs"
  shows "ev_ro xs ! ev_tag = xs ! ro_lp"
proof -
  have idx: "ev_tag
      = length (hl (seg ro_lp L xs))
        + (length (concat (map (\<lambda>l. hn (ro_mxl xs l) (ro_mxr xs l)) [0 ..< dd]))
        + (length (concat (map (\<lambda>l. seg (ro_acc l) W xs) [0 ..< Suc dd]))
        + (length (map (\<lambda>l. xs ! ro_kb l) [0 ..< dd])
        + (length (seg ro_root W xs)
        + (length (seg ro_vd W xs)
        + 0)))))"
    using ev_ro_block_lens[OF len] length_seg_ro(4)[OF len] length_seg_ro(5)[OF len]
    by (simp add: ev_tag_def ev_vd_def ev_root_def algebra_simps)
  show ?thesis
    unfolding ev_ro_def pad_to_def ev_ro_core_def idx append_assoc
    by (simp only: nth_append_length_plus) simp
qed

subsection \<open>Update slots\<close>

lemma up_seg_bounds:
  "up_lp + L \<le> up_width"
  "up_lp2 + L \<le> up_width"
  "l \<le> dd \<Longrightarrow> up_acc l + W \<le> up_width"
  "l \<le> dd \<Longrightarrow> up_acc2 l + W \<le> up_width"
  "l < dd \<Longrightarrow> up_sib l + W \<le> up_width"
  "l < dd \<Longrightarrow> up_kb l < up_width"
  "up_root + W \<le> up_width"
  "up_root2 + W \<le> up_width"
  "up_vd + W \<le> up_width"
proof -
  have d2: "W * (dd + 1) = W * dd + W"
    by (simp add: algebra_simps)
  have d3: "W * (3 * dd + 2) = 3 * (W * dd) + 2 * W"
    by (simp add: algebra_simps)
  have d4: "2 * W * (dd + 1) = 2 * (W * dd) + 2 * W"
    by (simp add: algebra_simps)
  show "up_lp + L \<le> up_width"
    unfolding up_lp_def up_width_def up_vd_def up_root2_def up_root_def by linarith
  show "up_lp2 + L \<le> up_width"
    unfolding up_lp2_def up_width_def up_vd_def up_root2_def up_root_def by linarith
  show "up_acc l + W \<le> up_width" if l: "l \<le> dd"
  proof -
    have m: "W * l \<le> W * dd" using l by (rule mult_le_mono2)
    show ?thesis
      using m d3
      unfolding up_acc_def up_width_def up_vd_def up_root2_def up_root_def
      by linarith
  qed
  show "up_acc2 l + W \<le> up_width" if l: "l \<le> dd"
  proof -
    have "W * l \<le> W * dd" using l by (rule mult_le_mono2)
    then have "W * (dd + 1) + W * l \<le> W * (dd + 1) + W * dd"
      by (rule add_left_mono)
    also have "W * (dd + 1) + W * dd = W * (2 * dd + 1)"
      by (simp add: algebra_simps)
    also have "W * (2 * dd + 1) \<le> W * (3 * dd + 2)"
      by (rule mult_le_mono2) linarith
    finally have m: "W * (dd + 1) + W * l \<le> W * (3 * dd + 2)" .
    show ?thesis
      using m
      unfolding up_acc2_def up_width_def up_vd_def up_root2_def up_root_def
      by linarith
  qed
  show "up_sib l + W \<le> up_width" if l: "l < dd"
  proof -
    have m: "W * l \<le> W * dd" using less_imp_le[OF l] by (rule mult_le_mono2)
    show ?thesis
      using m d3 d4
      unfolding up_sib_def up_width_def up_vd_def up_root2_def up_root_def
      by linarith
  qed
  show "up_kb l < up_width" if l: "l < dd"
    using l
    unfolding up_kb_def up_width_def up_vd_def up_root2_def up_root_def
    by linarith
  show "up_root + W \<le> up_width"
    unfolding up_width_def up_vd_def up_root2_def by linarith
  show "up_root2 + W \<le> up_width"
    unfolding up_width_def up_vd_def by linarith
  show "up_vd + W \<le> up_width"
    unfolding up_width_def by linarith
qed

lemma length_seg_up [simp]:
  assumes "up_width \<le> length xs"
  shows "length (seg up_lp L xs) = L"
    and "length (seg up_lp2 L xs) = L"
    and "l \<le> dd \<Longrightarrow> length (seg (up_acc l) W xs) = W"
    and "l \<le> dd \<Longrightarrow> length (seg (up_acc2 l) W xs) = W"
    and "l < dd \<Longrightarrow> length (seg (up_sib l) W xs) = W"
    and "length (seg up_root W xs) = W"
    and "length (seg up_root2 W xs) = W"
    and "length (seg up_vd W xs) = W"
proof -
  show "length (seg up_lp L xs) = L"
    by (rule length_seg) (rule le_trans[OF up_seg_bounds(1) assms])
  show "length (seg up_lp2 L xs) = L"
    by (rule length_seg) (rule le_trans[OF up_seg_bounds(2) assms])
  show "length (seg (up_acc l) W xs) = W" if l: "l \<le> dd"
    by (rule length_seg) (rule le_trans[OF up_seg_bounds(3)[OF l] assms])
  show "length (seg (up_acc2 l) W xs) = W" if l: "l \<le> dd"
    by (rule length_seg) (rule le_trans[OF up_seg_bounds(4)[OF l] assms])
  show "length (seg (up_sib l) W xs) = W" if l: "l < dd"
    by (rule length_seg) (rule le_trans[OF up_seg_bounds(5)[OF l] assms])
  show "length (seg up_root W xs) = W"
    by (rule length_seg) (rule le_trans[OF up_seg_bounds(7) assms])
  show "length (seg up_root2 W xs) = W"
    by (rule length_seg) (rule le_trans[OF up_seg_bounds(8) assms])
  show "length (seg up_vd W xs) = W"
    by (rule length_seg) (rule le_trans[OF up_seg_bounds(9) assms])
qed

lemma ev_up_block_lens:
  assumes "up_width \<le> length xs"
  shows "length (concat (map (\<lambda>l. hn (up_mxl xs up_acc l) (up_mxr xs up_acc l)) [0 ..< dd])) = dd * W"
    and "length (concat (map (\<lambda>l. hn (up_mxl xs up_acc2 l) (up_mxr xs up_acc2 l)) [0 ..< dd])) = dd * W"
    and "length (concat (map (\<lambda>l. seg (up_acc l) W xs) [0 ..< Suc dd])) = Suc dd * W"
    and "length (concat (map (\<lambda>l. seg (up_acc2 l) W xs) [0 ..< Suc dd])) = Suc dd * W"
  using assms
  by (auto intro!: concat_map_uniform_length simp: length_seg up_seg_bounds
           intro: order_trans)

lemma length_ev_up_core:
  assumes len: "up_width \<le> length xs"
  shows "length (ev_up_core xs) = ev_up_len"
  using ev_up_block_lens[OF len] length_seg_up[OF len]
  by (simp add: ev_up_core_def ev_up_len_def ev2_vd_def ev2_root2_def ev2_root_def
                algebra_simps)

lemma length_ev_up:
  assumes len: "up_width \<le> length xs"
  shows "length (ev_up xs) = 2 ^ ev_up_len"
  by (simp add: ev_up_def length_pad_to length_ev_up_core[OF len]
                less_imp_le[OF less_exp])

lemma ev_up_nth_hl:
  assumes len: "up_width \<le> length xs" and i: "i < W"
  shows "ev_up xs ! (ev2_hl + i) = hl (seg up_lp L xs) ! i"
    and "ev_up xs ! (ev2_hl2 + i) = hl (seg up_lp2 L xs) ! i"
  using i by (simp_all add: ev_up_def pad_to_def ev_up_core_def ev2_hl_def
                            ev2_hl2_def nth_append)

lemma ev_up_nth_hn:
  assumes len: "up_width \<le> length xs" and l: "l < dd" and i: "i < W"
  shows "ev_up xs ! (ev2_hn l + i) = hn (up_mxl xs up_acc l) (up_mxr xs up_acc l) ! i"
proof -
  have lt: "W * l + i < dd * W" using block_index_lt l i by simp
  have "ev_up xs ! (ev2_hn l + i)
        = concat (map (\<lambda>j. hn (up_mxl xs up_acc j) (up_mxr xs up_acc j)) [0 ..< dd]) ! (W * l + i)"
    using lt by (simp add: ev_up_def pad_to_def ev_up_core_def ev2_hn_def nth_append
                           ev_up_block_lens[OF len] algebra_simps)
  also have "\<dots> = hn (up_mxl xs up_acc l) (up_mxr xs up_acc l) ! i"
    using l i by (subst mult.commute[of W l]) (intro concat_map_uniform_nth; simp)
  finally show ?thesis .
qed

lemma ev_up_nth_hn2:
  assumes len: "up_width \<le> length xs" and l: "l < dd" and i: "i < W"
  shows "ev_up xs ! (ev2_hn2 l + i) = hn (up_mxl xs up_acc2 l) (up_mxr xs up_acc2 l) ! i"
proof -
  have lt: "W * l + i < dd * W" using block_index_lt l i by simp
  have "ev_up xs ! (ev2_hn2 l + i)
        = concat (map (\<lambda>j. hn (up_mxl xs up_acc2 j) (up_mxr xs up_acc2 j)) [0 ..< dd]) ! (W * l + i)"
    using lt by (simp add: ev_up_def pad_to_def ev_up_core_def ev2_hn2_def nth_append
                           ev_up_block_lens[OF len] algebra_simps)
  also have "\<dots> = hn (up_mxl xs up_acc2 l) (up_mxr xs up_acc2 l) ! i"
    using l i by (subst mult.commute[of W l]) (intro concat_map_uniform_nth; simp)
  finally show ?thesis .
qed

lemma ev_up_nth_acc:
  assumes len: "up_width \<le> length xs" and l: "l \<le> dd" and i: "i < W"
  shows "ev_up xs ! (ev2_acc l + i) = seg (up_acc l) W xs ! i"
proof -
  have lt: "W * l + i < Suc dd * W"
    by (rule block_index_lt[OF le_imp_less_Suc[OF l] i])
  have idx: "ev2_acc l + i
      = length (hl (seg up_lp L xs))
        + (length (hl (seg up_lp2 L xs))
        + (length (concat (map (\<lambda>l. hn (up_mxl xs up_acc l) (up_mxr xs up_acc l)) [0 ..< dd]))
        + (length (concat (map (\<lambda>l. hn (up_mxl xs up_acc2 l) (up_mxr xs up_acc2 l)) [0 ..< dd]))
        + (W * l + i))))"
    using ev_up_block_lens[OF len] by (simp add: ev2_acc_def algebra_simps)
  have lt2: "W * l + i < length (concat (map (\<lambda>l. seg (up_acc l) W xs) [0 ..< Suc dd]))"
    using ev_up_block_lens(3)[OF len] lt by simp
  have "ev_up xs ! (ev2_acc l + i)
        = concat (map (\<lambda>j. seg (up_acc j) W xs) [0 ..< Suc dd]) ! (W * l + i)"
    unfolding ev_up_def pad_to_def ev_up_core_def idx append_assoc
    by (simp only: nth_append_length_plus) (simp only: nth_append if_P[OF lt2])
  also have "\<dots> = seg (up_acc l) W xs ! i"
    using l i len
    by (subst mult.commute[of W l])
       (intro concat_map_uniform_nth; simp add: le_imp_less_Suc)
  finally show ?thesis .
qed

lemma ev_up_nth_acc2:
  assumes len: "up_width \<le> length xs" and l: "l \<le> dd" and i: "i < W"
  shows "ev_up xs ! (ev2_acc2 l + i) = seg (up_acc2 l) W xs ! i"
proof -
  have lt: "W * l + i < Suc dd * W"
    by (rule block_index_lt[OF le_imp_less_Suc[OF l] i])
  have idx: "ev2_acc2 l + i
      = length (hl (seg up_lp L xs))
        + (length (hl (seg up_lp2 L xs))
        + (length (concat (map (\<lambda>l. hn (up_mxl xs up_acc l) (up_mxr xs up_acc l)) [0 ..< dd]))
        + (length (concat (map (\<lambda>l. hn (up_mxl xs up_acc2 l) (up_mxr xs up_acc2 l)) [0 ..< dd]))
        + (length (concat (map (\<lambda>l. seg (up_acc l) W xs) [0 ..< Suc dd]))
        + (W * l + i)))))"
    using ev_up_block_lens[OF len] by (simp add: ev2_acc2_def algebra_simps)
  have lt2: "W * l + i < length (concat (map (\<lambda>l. seg (up_acc2 l) W xs) [0 ..< Suc dd]))"
    using ev_up_block_lens(4)[OF len] lt by simp
  have "ev_up xs ! (ev2_acc2 l + i)
        = concat (map (\<lambda>j. seg (up_acc2 j) W xs) [0 ..< Suc dd]) ! (W * l + i)"
    unfolding ev_up_def pad_to_def ev_up_core_def idx append_assoc
    by (simp only: nth_append_length_plus) (simp only: nth_append if_P[OF lt2])
  also have "\<dots> = seg (up_acc2 l) W xs ! i"
    using l i len
    by (subst mult.commute[of W l])
       (intro concat_map_uniform_nth; simp add: le_imp_less_Suc)
  finally show ?thesis .
qed

lemma ev_up_nth_kb:
  assumes len: "up_width \<le> length xs" and l: "l < dd"
  shows "ev_up xs ! (ev2_kb l) = xs ! up_kb l"
proof -
  have idx: "ev2_kb l
      = length (hl (seg up_lp L xs))
        + (length (hl (seg up_lp2 L xs))
        + (length (concat (map (\<lambda>l. hn (up_mxl xs up_acc l) (up_mxr xs up_acc l)) [0 ..< dd]))
        + (length (concat (map (\<lambda>l. hn (up_mxl xs up_acc2 l) (up_mxr xs up_acc2 l)) [0 ..< dd]))
        + (length (concat (map (\<lambda>l. seg (up_acc l) W xs) [0 ..< Suc dd]))
        + (length (concat (map (\<lambda>l. seg (up_acc2 l) W xs) [0 ..< Suc dd]))
        + l)))))"
    using ev_up_block_lens[OF len] by (simp add: ev2_kb_def algebra_simps)
  show ?thesis
    unfolding ev_up_def pad_to_def ev_up_core_def idx append_assoc
    by (simp only: nth_append_length_plus) (simp add: nth_append l nth_upt)
qed

lemma ev_up_nth_root:
  assumes len: "up_width \<le> length xs" and i: "i < W"
  shows "ev_up xs ! (ev2_root + i) = seg up_root W xs ! i"
proof -
  have idx: "ev2_root + i
      = length (hl (seg up_lp L xs))
        + (length (hl (seg up_lp2 L xs))
        + (length (concat (map (\<lambda>l. hn (up_mxl xs up_acc l) (up_mxr xs up_acc l)) [0 ..< dd]))
        + (length (concat (map (\<lambda>l. hn (up_mxl xs up_acc2 l) (up_mxr xs up_acc2 l)) [0 ..< dd]))
        + (length (concat (map (\<lambda>l. seg (up_acc l) W xs) [0 ..< Suc dd]))
        + (length (concat (map (\<lambda>l. seg (up_acc2 l) W xs) [0 ..< Suc dd]))
        + (length (map (\<lambda>l. xs ! up_kb l) [0 ..< dd])
        + i))))))"
    using ev_up_block_lens[OF len] by (simp add: ev2_root_def algebra_simps)
  show ?thesis
    unfolding ev_up_def pad_to_def ev_up_core_def idx append_assoc
    by (simp only: nth_append_length_plus)
       (simp add: nth_append length_seg_up(6)[OF len] i)
qed

lemma ev_up_nth_root2:
  assumes len: "up_width \<le> length xs" and i: "i < W"
  shows "ev_up xs ! (ev2_root2 + i) = seg up_root2 W xs ! i"
proof -
  have idx: "ev2_root2 + i
      = length (hl (seg up_lp L xs))
        + (length (hl (seg up_lp2 L xs))
        + (length (concat (map (\<lambda>l. hn (up_mxl xs up_acc l) (up_mxr xs up_acc l)) [0 ..< dd]))
        + (length (concat (map (\<lambda>l. hn (up_mxl xs up_acc2 l) (up_mxr xs up_acc2 l)) [0 ..< dd]))
        + (length (concat (map (\<lambda>l. seg (up_acc l) W xs) [0 ..< Suc dd]))
        + (length (concat (map (\<lambda>l. seg (up_acc2 l) W xs) [0 ..< Suc dd]))
        + (length (map (\<lambda>l. xs ! up_kb l) [0 ..< dd])
        + (length (seg up_root W xs)
        + i)))))))"
    using ev_up_block_lens[OF len] length_seg_up(6)[OF len]
    by (simp add: ev2_root2_def ev2_root_def algebra_simps)
  show ?thesis
    unfolding ev_up_def pad_to_def ev_up_core_def idx append_assoc
    by (simp only: nth_append_length_plus)
       (simp add: nth_append length_seg_up(7)[OF len] i)
qed

lemma ev_up_nth_vd:
  assumes len: "up_width \<le> length xs" and i: "i < W"
  shows "ev_up xs ! (ev2_vd + i) = seg up_vd W xs ! i"
proof -
  have idx: "ev2_vd + i
      = length (hl (seg up_lp L xs))
        + (length (hl (seg up_lp2 L xs))
        + (length (concat (map (\<lambda>l. hn (up_mxl xs up_acc l) (up_mxr xs up_acc l)) [0 ..< dd]))
        + (length (concat (map (\<lambda>l. hn (up_mxl xs up_acc2 l) (up_mxr xs up_acc2 l)) [0 ..< dd]))
        + (length (concat (map (\<lambda>l. seg (up_acc l) W xs) [0 ..< Suc dd]))
        + (length (concat (map (\<lambda>l. seg (up_acc2 l) W xs) [0 ..< Suc dd]))
        + (length (map (\<lambda>l. xs ! up_kb l) [0 ..< dd])
        + (length (seg up_root W xs)
        + (length (seg up_root2 W xs)
        + i))))))))"
    using ev_up_block_lens[OF len] length_seg_up(6)[OF len] length_seg_up(7)[OF len]
    by (simp add: ev2_vd_def ev2_root2_def ev2_root_def algebra_simps)
  show ?thesis
    unfolding ev_up_def pad_to_def ev_up_core_def idx append_assoc
    by (simp only: nth_append_length_plus)
       (simp add: nth_append length_seg_up(8)[OF len] i)
qed

section \<open>Stage A-i: acceptance is the constraint conjunction\<close>

text \<open>Vanishing of all residuals of \<open>descs_ro\<close> IS \<open>cons_ro\<close>.\<close>

lemma res_sem_descs_ro_iff:
  assumes len: "ro_width \<le> length xs"
  shows "(\<forall>rd \<in> set (descs_ro k). res_sem (ev_ro xs) rd = 0) \<longleftrightarrow> cons_ro k xs"
proof -
  let ?ev = "ev_ro xs"
  have leaf: "(\<forall>rd \<in> set (map (\<lambda>i. RDiff (ev_hl + i) (ev_acc 0 + i)) [0 ..< W]).
                 res_sem ?ev rd = 0)
              \<longleftrightarrow> hl (seg ro_lp L xs) = seg (ro_acc 0) W xs"
    using ev_ro_nth_hl[OF len] ev_ro_nth_acc[OF len, of 0]
    by (auto simp: list_eq_iff_nth_eq length_seg_ro[OF len])
  have chain: "(\<forall>rd \<in> set (concat (map (\<lambda>l. map (\<lambda>i. RDiff (ev_hn l + i) (ev_acc (Suc l) + i))
                                              [0 ..< W]) [0 ..< dd])).
                  res_sem ?ev rd = 0)
               \<longleftrightarrow> (\<forall>l<dd. hn (ro_mxl xs l) (ro_mxr xs l) = seg (ro_acc (Suc l)) W xs)"
  proof -
    have "(\<forall>rd \<in> set (concat (map (\<lambda>l. map (\<lambda>i. RDiff (ev_hn l + i) (ev_acc (Suc l) + i))
                                          [0 ..< W]) [0 ..< dd])).
             res_sem ?ev rd = 0)
          \<longleftrightarrow> (\<forall>l<dd. \<forall>i<W. ?ev ! (ev_hn l + i) = ?ev ! (ev_acc (Suc l) + i))"
      by auto
    also have "\<dots> \<longleftrightarrow> (\<forall>l<dd. hn (ro_mxl xs l) (ro_mxr xs l) = seg (ro_acc (Suc l)) W xs)"
    proof (intro all_cong1 imp_cong[OF refl])
      fix l assume "l < dd"
      then show "(\<forall>i<W. ?ev ! (ev_hn l + i) = ?ev ! (ev_acc (Suc l) + i))
                 \<longleftrightarrow> hn (ro_mxl xs l) (ro_mxr xs l) = seg (ro_acc (Suc l)) W xs"
        using ev_ro_nth_hn[OF len] ev_ro_nth_acc[OF len]
        by (auto simp: list_eq_iff_nth_eq length_seg_ro[OF len] Suc_le_eq)
    qed
    finally show ?thesis .
  qed
  have root: "(\<forall>rd \<in> set (map (\<lambda>i. RDiff (ev_acc dd + i) (ev_root + i)) [0 ..< W]).
                 res_sem ?ev rd = 0)
              \<longleftrightarrow> seg (ro_acc dd) W xs = seg ro_root W xs"
    using ev_ro_nth_acc[OF len, of dd] ev_ro_nth_root[OF len]
    by (auto simp: list_eq_iff_nth_eq length_seg_ro[OF len])
  have vd: "(\<forall>rd \<in> set (map (\<lambda>i. RDiff (ev_acc 0 + i) (ev_vd + i)) [0 ..< W]).
               res_sem ?ev rd = 0)
            \<longleftrightarrow> seg (ro_acc 0) W xs = seg ro_vd W xs"
    using ev_ro_nth_acc[OF len, of 0] ev_ro_nth_vd[OF len]
    by (auto simp: list_eq_iff_nth_eq length_seg_ro[OF len])
  have bool: "(\<forall>rd \<in> set (map (\<lambda>l. RBool (ev_kb l)) [0 ..< dd]). res_sem ?ev rd = 0)
              \<longleftrightarrow> (\<forall>l<dd. xs ! ro_kb l * (xs ! ro_kb l - 1) = 0)"
    using ev_ro_nth_kb[OF len] by (auto simp: algebra_simps)
  have tag: "(\<forall>rd \<in> set (if k = KNonMembership then [RTag ev_tag] else []).
                res_sem ?ev rd = 0)
             \<longleftrightarrow> (k = KNonMembership \<longrightarrow> xs ! ro_lp * (xs ! ro_lp - 2) = 0)"
    using ev_ro_nth_tag[OF len] by (auto simp: algebra_simps)
  show ?thesis
    unfolding descs_ro_def cons_ro_def set_append ball_Un
    using leaf chain root vd bool tag by blast
qed

end

context compiler_model
begin

theorem A_i_ro:
  assumes k: "k \<noteq> KUpdate" and len: "length xs = ivlen k"
  shows "circuit_accept (compile k) xs \<longleftrightarrow> cons_ro k xs"
proof -
  have wk: "in_width k = ro_width" using k by (cases k) auto
  have lenw: "ro_width \<le> length xs"
    using len in_width_le_ivlen[of k] wk by simp
  have dk: "descs k = descs_ro k" using k by (cases k) auto
  have "circuit_accept (compile k) xs
        \<longleftrightarrow> (\<forall>v \<in> set (layer_eval (mk_res_layer (descs_ro k)) (ev_ro xs)). v = 0)"
    by (simp add: circuit_accept_def compile_output[OF len] stack_spec_ro[OF k len] dk)
  also have "\<dots> \<longleftrightarrow> (\<forall>rd \<in> set (descs_ro k). res_sem (ev_ro xs) rd = 0)"
    by (rule mk_res_layer_accept_iff)
  also have "\<dots> \<longleftrightarrow> cons_ro k xs"
    by (rule res_sem_descs_ro_iff[OF lenw])
  finally show ?thesis .
qed

lemma res_sem_descs_up_iff:
  assumes len: "up_width \<le> length xs"
  shows "(\<forall>rd \<in> set descs_up. res_sem (ev_up xs) rd = 0) \<longleftrightarrow> cons_up xs"
proof -
  let ?ev = "ev_up xs"
  have leaf: "(\<forall>rd \<in> set (map (\<lambda>i. RDiff (ev2_hl + i) (ev2_acc 0 + i)) [0 ..< W]).
                 res_sem ?ev rd = 0)
              \<longleftrightarrow> hl (seg up_lp L xs) = seg (up_acc 0) W xs"
    using ev_up_nth_hl[OF len] ev_up_nth_acc[OF len, of 0]
    by (auto simp: list_eq_iff_nth_eq length_seg_up[OF len])
  have leaf2: "(\<forall>rd \<in> set (map (\<lambda>i. RDiff (ev2_hl2 + i) (ev2_acc2 0 + i)) [0 ..< W]).
                  res_sem ?ev rd = 0)
               \<longleftrightarrow> hl (seg up_lp2 L xs) = seg (up_acc2 0) W xs"
    using ev_up_nth_hl[OF len] ev_up_nth_acc2[OF len, of 0]
    by (auto simp: list_eq_iff_nth_eq length_seg_up[OF len])
  have chain: "(\<forall>rd \<in> set (concat (map (\<lambda>l. map (\<lambda>i. RDiff (ev2_hn l + i) (ev2_acc (Suc l) + i))
                                              [0 ..< W]) [0 ..< dd])).
                  res_sem ?ev rd = 0)
               \<longleftrightarrow> (\<forall>l<dd. hn (up_mxl xs up_acc l) (up_mxr xs up_acc l)
                           = seg (up_acc (Suc l)) W xs)"
  proof -
    have "(\<forall>rd \<in> set (concat (map (\<lambda>l. map (\<lambda>i. RDiff (ev2_hn l + i) (ev2_acc (Suc l) + i))
                                          [0 ..< W]) [0 ..< dd])).
             res_sem ?ev rd = 0)
          \<longleftrightarrow> (\<forall>l<dd. \<forall>i<W. ?ev ! (ev2_hn l + i) = ?ev ! (ev2_acc (Suc l) + i))"
      by auto
    also have "\<dots> \<longleftrightarrow> (\<forall>l<dd. hn (up_mxl xs up_acc l) (up_mxr xs up_acc l)
                              = seg (up_acc (Suc l)) W xs)"
    proof (intro all_cong1 imp_cong[OF refl])
      fix l assume "l < dd"
      then show "(\<forall>i<W. ?ev ! (ev2_hn l + i) = ?ev ! (ev2_acc (Suc l) + i))
                 \<longleftrightarrow> hn (up_mxl xs up_acc l) (up_mxr xs up_acc l) = seg (up_acc (Suc l)) W xs"
        using ev_up_nth_hn[OF len] ev_up_nth_acc[OF len]
        by (auto simp: list_eq_iff_nth_eq length_seg_up[OF len] Suc_le_eq)
    qed
    finally show ?thesis .
  qed
  have chain2: "(\<forall>rd \<in> set (concat (map (\<lambda>l. map (\<lambda>i. RDiff (ev2_hn2 l + i) (ev2_acc2 (Suc l) + i))
                                               [0 ..< W]) [0 ..< dd])).
                   res_sem ?ev rd = 0)
                \<longleftrightarrow> (\<forall>l<dd. hn (up_mxl xs up_acc2 l) (up_mxr xs up_acc2 l)
                            = seg (up_acc2 (Suc l)) W xs)"
  proof -
    have "(\<forall>rd \<in> set (concat (map (\<lambda>l. map (\<lambda>i. RDiff (ev2_hn2 l + i) (ev2_acc2 (Suc l) + i))
                                          [0 ..< W]) [0 ..< dd])).
             res_sem ?ev rd = 0)
          \<longleftrightarrow> (\<forall>l<dd. \<forall>i<W. ?ev ! (ev2_hn2 l + i) = ?ev ! (ev2_acc2 (Suc l) + i))"
      by auto
    also have "\<dots> \<longleftrightarrow> (\<forall>l<dd. hn (up_mxl xs up_acc2 l) (up_mxr xs up_acc2 l)
                              = seg (up_acc2 (Suc l)) W xs)"
    proof (intro all_cong1 imp_cong[OF refl])
      fix l assume "l < dd"
      then show "(\<forall>i<W. ?ev ! (ev2_hn2 l + i) = ?ev ! (ev2_acc2 (Suc l) + i))
                 \<longleftrightarrow> hn (up_mxl xs up_acc2 l) (up_mxr xs up_acc2 l) = seg (up_acc2 (Suc l)) W xs"
        using ev_up_nth_hn2[OF len] ev_up_nth_acc2[OF len]
        by (auto simp: list_eq_iff_nth_eq length_seg_up[OF len] Suc_le_eq)
    qed
    finally show ?thesis .
  qed
  have root: "(\<forall>rd \<in> set (map (\<lambda>i. RDiff (ev2_acc dd + i) (ev2_root + i)) [0 ..< W]).
                 res_sem ?ev rd = 0)
              \<longleftrightarrow> seg (up_acc dd) W xs = seg up_root W xs"
    using ev_up_nth_acc[OF len, of dd] ev_up_nth_root[OF len]
    by (auto simp: list_eq_iff_nth_eq length_seg_up[OF len])
  have root2: "(\<forall>rd \<in> set (map (\<lambda>i. RDiff (ev2_acc2 dd + i) (ev2_root2 + i)) [0 ..< W]).
                  res_sem ?ev rd = 0)
               \<longleftrightarrow> seg (up_acc2 dd) W xs = seg up_root2 W xs"
    using ev_up_nth_acc2[OF len, of dd] ev_up_nth_root2[OF len]
    by (auto simp: list_eq_iff_nth_eq length_seg_up[OF len])
  have vd: "(\<forall>rd \<in> set (map (\<lambda>i. RDiff (ev2_acc2 0 + i) (ev2_vd + i)) [0 ..< W]).
               res_sem ?ev rd = 0)
            \<longleftrightarrow> seg (up_acc2 0) W xs = seg up_vd W xs"
    using ev_up_nth_acc2[OF len, of 0] ev_up_nth_vd[OF len]
    by (auto simp: list_eq_iff_nth_eq length_seg_up[OF len])
  have bool: "(\<forall>rd \<in> set (map (\<lambda>l. RBool (ev2_kb l)) [0 ..< dd]). res_sem ?ev rd = 0)
              \<longleftrightarrow> (\<forall>l<dd. xs ! up_kb l * (xs ! up_kb l - 1) = 0)"
    using ev_up_nth_kb[OF len] by (auto simp: algebra_simps)
  show ?thesis
    unfolding descs_up_def cons_up_def set_append ball_Un
    using leaf leaf2 chain chain2 root root2 vd bool by blast
qed

theorem A_i_up:
  assumes len: "length xs = ivlen KUpdate"
  shows "circuit_accept (compile KUpdate) xs \<longleftrightarrow> cons_up xs"
proof -
  have lenw: "up_width \<le> length xs"
    using len in_width_le_ivlen[of KUpdate] by simp
  have "circuit_accept (compile KUpdate) xs
        \<longleftrightarrow> (\<forall>v \<in> set (layer_eval (mk_res_layer descs_up) (ev_up xs)). v = 0)"
    by (simp add: circuit_accept_def compile_output[OF len] stack_spec_up[OF len])
  also have "\<dots> \<longleftrightarrow> (\<forall>rd \<in> set descs_up. res_sem (ev_up xs) rd = 0)"
    by (rule mk_res_layer_accept_iff)
  also have "\<dots> \<longleftrightarrow> cons_up xs"
    by (rule res_sem_descs_up_iff[OF lenw])
  finally show ?thesis .
qed

end

section \<open>Stage A-ii: the constraint conjunction is the SMT semantics\<close>

text \<open>
  Stage A-i reduced circuit acceptance to the constraint conjunctions
  \<open>cons_ro\<close>/\<open>cons_up\<close> over the evaluation-stack vector.  Stage A-ii
  evaluates those conjunctions on the HONEST witness encoding
  (\<open>enc_ro\<close>/\<open>enc_up\<close>, the literal \<open>build_input_vector\<close> transcription):
  the hash-binding, chain and booleanity clauses hold by construction
  (the encoder computes the honest accumulator chain), so the
  conjunction collapses to exactly the semantic equations - path
  equality, value-digest binding and (NonMembership) the leaf-tag
  domain.  Together with the facade public-input checks (the
  \<open>verifier_accept\<close> model below, Rust: \<open>verify_sync_op\<close>) this yields
  Theorem A.
\<close>

subsection \<open>Theory-level helpers\<close>

text \<open>The operation's asset key.  Rust: \<open>op_key\<close> (witness.rs).\<close>

fun op_key :: "'v smt_op \<Rightarrow> nat" where
  "op_key (Membership k v) = k"
| "op_key (NonMembership k) = k"
| "op_key (Update k old new) = k"

text \<open>
  The tag residual \<open>tag * (tag - 2)\<close> vanishes on the leaf-tag lane
  exactly for the Empty/Tombstone states - the circuit-immanent
  NonMembership domain separation.  Occupied has tag 1, and 1 is neither
  0 nor 2 in ANY ring with \<open>0 \<noteq> 1\<close> (\<open>1 = 2\<close> would force \<open>0 = 1\<close>), so no
  characteristic assumption is needed.  Stated in the disjunctive form
  the simplifier's \<open>mult_eq_0_iff\<close> normalisation produces.
\<close>

lemma leaf_tag_val_zero_or_two:
  "((leaf_tag_val lf :: 'f::comm_ring_1) = 0 \<or> (leaf_tag_val lf :: 'f) = 2)
   \<longleftrightarrow> (lf = Empty \<or> lf = Tombstone)"
proof (cases lf)
  case (Occupied v)
  have neq2: "(1 :: 'f) \<noteq> 2"
  proof
    assume a: "(1 :: 'f) = 2"
    have "(1 :: 'f) + 0 = 1 + 1" using a by (simp add: one_add_one)
    then have "(0 :: 'f) = 1" by (rule add_left_imp_eq)
    then show False by simp
  qed
  then show ?thesis by (simp add: Occupied)
qed simp_all

text \<open>Extracting one block out of an explicit append decomposition.\<close>

lemma seg_at:
  "length pre = a \<Longrightarrow> length blk = w \<Longrightarrow> seg a w (pre @ blk @ post) = blk"
  by (simp add: seg_def)

lemma nth_at:
  "length pre = a \<Longrightarrow> i < length blk \<Longrightarrow> (pre @ blk @ post) ! (a + i) = blk ! i"
  by (simp add: nth_append)

lemma concat_map_upt_split:
  assumes "l < n"
  shows "concat (map f [0 ..< n])
         = concat (map f [0 ..< l]) @ f l @ concat (map f [Suc l ..< n])"
proof -
  from assms have n_decomp: "n = l + Suc (n - Suc l)" by arith
  have "[0 ..< l + Suc (n - Suc l)] = [0 ..< l] @ [l ..< l + Suc (n - Suc l)]"
    by (rule upt_add_eq_append) simp
  moreover have "[l ..< l + Suc (n - Suc l)] = l # [Suc l ..< l + Suc (n - Suc l)]"
    by (rule upt_conv_Cons) simp
  ultimately have "[0 ..< n] = [0 ..< l] @ l # [Suc l ..< n]"
    using n_decomp by simp
  then show ?thesis by simp
qed

context compiler_model_base
begin

subsection \<open>Segment values of the read-only encoding\<close>

lemma length_enc_ro_core:
  "length (enc_ro_core leaf key sibs root vd) = ro_width"
proof -
  have acc: "length (concat (map (\<lambda>l. digest_repr (acc_list (h_leaf leaf) key sibs ! l))
                                 [0 ..< Suc dd])) = Suc dd * W"
    by (intro concat_map_uniform_length) simp
  have sib: "length (concat (map (\<lambda>l. digest_repr (sibs ! l)) [0 ..< dd])) = dd * W"
    by (intro concat_map_uniform_length) simp
  show ?thesis
    unfolding enc_ro_core_def ro_width_def ro_vd_def ro_root_def
    by (simp only: length_append acc sib length_map length_upt digest_len leaf_len)
       (simp add: algebra_simps)
qed

lemma length_enc_ro:
  assumes "k \<noteq> KUpdate"
  shows "length (enc_ro k leaf key sibs root vd) = ivlen k"
proof -
  have "in_width k = ro_width" using assms by (cases k) auto
  then have "length (enc_ro_core leaf key sibs root vd) \<le> ivlen k"
    using in_width_le_ivlen[of k] by (simp add: length_enc_ro_core)
  then show ?thesis by (simp add: enc_ro_def length_pad_to)
qed

lemma enc_ro_core_segs:
  fixes leaf :: "'v leaf_state" and key :: nat and sibs :: "'d list" and root vd :: 'd
  defines "xs \<equiv> enc_ro_core leaf key sibs root vd"
  shows enc_ro_core_lp: "seg ro_lp L xs = leaf_repr leaf"
    and enc_ro_core_acc:
      "\<And>l. l \<le> dd \<Longrightarrow> seg (ro_acc l) W xs
                       = digest_repr (acc_list (h_leaf leaf) key sibs ! l)"
    and enc_ro_core_sib:
      "\<And>l. l < dd \<Longrightarrow> seg (ro_sib l) W xs = digest_repr (sibs ! l)"
    and enc_ro_core_kb: "\<And>l. l < dd \<Longrightarrow> xs ! ro_kb l = kbit key l"
    and enc_ro_core_root: "seg ro_root W xs = digest_repr root"
    and enc_ro_core_vd: "seg ro_vd W xs = digest_repr vd"
    and enc_ro_core_tag: "xs ! ro_lp = leaf_tag_val leaf"
proof -
  let ?f = "\<lambda>l. digest_repr (acc_list (h_leaf leaf) key sibs ! l)"
  let ?g = "\<lambda>l. digest_repr (sibs ! l)"
  let ?ACC = "concat (map ?f [0 ..< Suc dd])"
  let ?SIB = "concat (map ?g [0 ..< dd])"
  let ?KB = "map (kbit key) [0 ..< dd] :: 'f list"
  have xs_eq: "xs = leaf_repr leaf @ ?ACC @ ?SIB @ ?KB
                    @ digest_repr root @ digest_repr vd"
    by (simp add: xs_def enc_ro_core_def)
  have lACC: "length ?ACC = Suc dd * W"
    by (intro concat_map_uniform_length) simp
  have lSIB: "length ?SIB = dd * W"
    by (intro concat_map_uniform_length) simp

  show "seg ro_lp L xs = leaf_repr leaf"
    unfolding xs_eq ro_lp_def by (simp add: seg_def)

  show "seg (ro_acc l) W xs = ?f l" if l: "l \<le> dd" for l
  proof -
    have split: "?ACC = concat (map ?f [0 ..< l]) @ ?f l @ concat (map ?f [Suc l ..< Suc dd])"
      by (rule concat_map_upt_split) (simp add: le_imp_less_Suc[OF l])
    have xs2: "xs = (leaf_repr leaf @ concat (map ?f [0 ..< l])) @ ?f l
                    @ (concat (map ?f [Suc l ..< Suc dd]) @ ?SIB @ ?KB
                       @ digest_repr root @ digest_repr vd)"
      unfolding xs_eq split by simp
    have lblk: "length (concat (map ?f [0 ..< l])) = l * W"
      by (intro concat_map_uniform_length) simp
    have lpre: "length (leaf_repr leaf @ concat (map ?f [0 ..< l])) = ro_acc l"
      by (simp add: lblk ro_acc_def mult.commute)
    show ?thesis unfolding xs2 by (rule seg_at[OF lpre]) simp
  qed

  show "seg (ro_sib l) W xs = ?g l" if l: "l < dd" for l
  proof -
    have split: "?SIB = concat (map ?g [0 ..< l]) @ ?g l @ concat (map ?g [Suc l ..< dd])"
      by (rule concat_map_upt_split) (rule l)
    have xs2: "xs = (leaf_repr leaf @ ?ACC @ concat (map ?g [0 ..< l])) @ ?g l
                    @ (concat (map ?g [Suc l ..< dd]) @ ?KB
                       @ digest_repr root @ digest_repr vd)"
      unfolding xs_eq split by simp
    have lblk: "length (concat (map ?g [0 ..< l])) = l * W"
      by (intro concat_map_uniform_length) simp
    have lpre: "length (leaf_repr leaf @ ?ACC @ concat (map ?g [0 ..< l])) = ro_sib l"
      unfolding ro_sib_def
      by (simp only: length_append lACC lblk leaf_len) (simp add: algebra_simps)
    show ?thesis unfolding xs2 by (rule seg_at[OF lpre]) simp
  qed

  show "xs ! ro_kb l = kbit key l" if l: "l < dd" for l
  proof -
    have xs2: "xs = (leaf_repr leaf @ ?ACC @ ?SIB) @ ?KB
                    @ (digest_repr root @ digest_repr vd)"
      unfolding xs_eq by simp
    have lpre: "length (leaf_repr leaf @ ?ACC @ ?SIB) = L + W * (2 * dd + 1)"
      by (simp only: length_append lACC lSIB leaf_len) (simp add: algebra_simps)
    have "xs ! (L + W * (2 * dd + 1) + l) = ?KB ! l"
      unfolding xs2 by (rule nth_at[OF lpre]) (simp add: l)
    then show ?thesis using l by (simp add: ro_kb_def)
  qed

  show "seg ro_root W xs = digest_repr root"
  proof -
    have xs2: "xs = (leaf_repr leaf @ ?ACC @ ?SIB @ ?KB) @ digest_repr root
                    @ digest_repr vd"
      unfolding xs_eq by simp
    have lpre: "length (leaf_repr leaf @ ?ACC @ ?SIB @ ?KB) = ro_root"
      unfolding ro_root_def
      by (simp only: length_append lACC lSIB leaf_len length_map length_upt)
         (simp add: algebra_simps)
    show ?thesis unfolding xs2 by (rule seg_at[OF lpre]) simp
  qed

  show "seg ro_vd W xs = digest_repr vd"
  proof -
    have xs2: "xs = (leaf_repr leaf @ ?ACC @ ?SIB @ ?KB @ digest_repr root)
                    @ digest_repr vd @ []"
      unfolding xs_eq by simp
    have lpre: "length (leaf_repr leaf @ ?ACC @ ?SIB @ ?KB @ digest_repr root) = ro_vd"
      unfolding ro_vd_def ro_root_def
      by (simp only: length_append lACC lSIB leaf_len length_map length_upt
                     digest_len)
         (simp add: algebra_simps)
    show ?thesis unfolding xs2 by (rule seg_at[OF lpre]) simp
  qed

  show "xs ! ro_lp = leaf_tag_val leaf"
    using L_pos leaf_tag[of leaf]
    unfolding xs_eq ro_lp_def
    by (simp add: nth_append)
qed

lemma enc_ro_segs:
  fixes leaf :: "'v leaf_state" and key :: nat and sibs :: "'d list" and root vd :: 'd
  assumes k: "k \<noteq> KUpdate"
  defines "xs \<equiv> enc_ro k leaf key sibs root vd"
  shows enc_ro_lp: "seg ro_lp L xs = leaf_repr leaf"
    and enc_ro_acc:
      "\<And>l. l \<le> dd \<Longrightarrow> seg (ro_acc l) W xs
                       = digest_repr (acc_list (h_leaf leaf) key sibs ! l)"
    and enc_ro_sib:
      "\<And>l. l < dd \<Longrightarrow> seg (ro_sib l) W xs = digest_repr (sibs ! l)"
    and enc_ro_kb: "\<And>l. l < dd \<Longrightarrow> xs ! ro_kb l = kbit key l"
    and enc_ro_root: "seg ro_root W xs = digest_repr root"
    and enc_ro_vd: "seg ro_vd W xs = digest_repr vd"
    and enc_ro_tag: "xs ! ro_lp = leaf_tag_val leaf"
proof -
  let ?core = "enc_ro_core leaf key sibs root vd"
  have lcore: "length ?core = ro_width" by (rule length_enc_ro_core)
  have xs_pad: "xs = pad_to (ivlen k) ?core" by (simp add: xs_def enc_ro_def)
  have segP: "a + w \<le> ro_width \<Longrightarrow> seg a w xs = seg a w ?core" for a w
    unfolding xs_pad by (rule seg_pad_to) (simp add: lcore)
  have nthP: "i < ro_width \<Longrightarrow> xs ! i = ?core ! i" for i
    unfolding xs_pad by (rule pad_to_nth) (simp add: lcore)
  show "seg ro_lp L xs = leaf_repr leaf"
    using segP[OF ro_seg_bounds(1)] enc_ro_core_lp by simp
  show "seg (ro_acc l) W xs = digest_repr (acc_list (h_leaf leaf) key sibs ! l)"
    if l: "l \<le> dd" for l
    using segP[OF ro_seg_bounds(2)[OF l]] enc_ro_core_acc[OF l] by simp
  show "seg (ro_sib l) W xs = digest_repr (sibs ! l)" if l: "l < dd" for l
    using segP[OF ro_seg_bounds(3)[OF l]] enc_ro_core_sib[OF l] by simp
  show "xs ! ro_kb l = kbit key l" if l: "l < dd" for l
    using nthP[OF ro_seg_bounds(4)[OF l]] enc_ro_core_kb[OF l] by simp
  show "seg ro_root W xs = digest_repr root"
    using segP[OF ro_seg_bounds(5)] enc_ro_core_root by simp
  show "seg ro_vd W xs = digest_repr vd"
    using segP[OF ro_seg_bounds(6)] enc_ro_core_vd by simp
  have lp_lt: "ro_lp < ro_width"
    using L_pos ro_seg_bounds(1) by (simp add: ro_lp_def)
  show "xs ! ro_lp = leaf_tag_val leaf"
    using nthP[OF lp_lt] enc_ro_core_tag by simp
qed

subsection \<open>The read-only constraint conjunction on the honest encoding\<close>

text \<open>
  On \<open>enc_ro\<close> the hash-binding, chain and booleanity clauses hold by
  construction (the encoder computes the honest accumulator chain), so
  \<open>cons_ro\<close> collapses to: path equality, value-digest binding, and (for
  NonMembership) the leaf-tag domain.
\<close>

lemma cons_ro_enc:
  assumes k: "k \<noteq> KUpdate" and sl: "length sibs = dd"
  shows "cons_ro k (enc_ro k leaf key sibs root vd) \<longleftrightarrow>
           (path_root (h_leaf leaf) key sibs = root \<and> vd = h_leaf leaf \<and>
            (k = KNonMembership \<longrightarrow> leaf = Empty \<or> leaf = Tombstone))"
proof -
  let ?xs = "enc_ro k leaf key sibs root vd"
  let ?acc = "acc_list (h_leaf leaf) key sibs"
  have dig_iff: "digest_repr x = digest_repr y \<longleftrightarrow> x = y" for x y
    using digest_inj by auto

  have c1: "hl (seg ro_lp L ?xs) = seg (ro_acc 0) W ?xs"
    using enc_ro_lp[OF k] enc_ro_acc[OF k, of 0]
    by (simp add: hl_correct)

  have c2: "hn (ro_mxl ?xs l) (ro_mxr ?xs l) = seg (ro_acc (Suc l)) W ?xs"
    if l: "l < dd" for l
  proof -
    have accl: "seg (ro_acc l) W ?xs = digest_repr (?acc ! l)"
      using enc_ro_acc[OF k] l by simp
    have accSl: "seg (ro_acc (Suc l)) W ?xs = digest_repr (?acc ! Suc l)"
      using enc_ro_acc[OF k] l by (simp add: Suc_le_eq)
    have sibl: "seg (ro_sib l) W ?xs = digest_repr (sibs ! l)"
      using enc_ro_sib[OF k] l by simp
    have kbl: "?xs ! ro_kb l = kbit key l"
      using enc_ro_kb[OF k] l by simp
    have step: "?acc ! Suc l =
                  (if (key div 2 ^ l) mod 2 = 0
                   then h_node (?acc ! l) (sibs ! l)
                   else h_node (sibs ! l) (?acc ! l))"
      by (rule acc_list_step) (simp add: sl l)
    show ?thesis
    proof (cases "(key div 2 ^ l) mod 2 = 0")
      case True
      have sel: "?xs ! ro_kb l = 0"
        using True by (simp add: kbl kbit_def)
      have mxl: "ro_mxl ?xs l = digest_repr (?acc ! l)"
        by (simp add: ro_mxl_def sel accl sibl mux_zero)
      have mxr: "ro_mxr ?xs l = digest_repr (sibs ! l)"
        by (simp add: ro_mxr_def sel accl sibl mux_zero)
      have "hn (ro_mxl ?xs l) (ro_mxr ?xs l)
            = digest_repr (h_node (?acc ! l) (sibs ! l))"
        by (simp add: mxl mxr hn_correct)
      with step True accSl show ?thesis by simp
    next
      case False
      have lt2: "(key div 2 ^ l) mod 2 < 2" by simp
      with False have m1: "(key div 2 ^ l) mod 2 = 1" by arith
      have sel: "?xs ! ro_kb l = 1"
        by (simp add: kbl kbit_def m1)
      have mxl: "ro_mxl ?xs l = digest_repr (sibs ! l)"
        by (simp add: ro_mxl_def sel accl sibl mux_one)
      have mxr: "ro_mxr ?xs l = digest_repr (?acc ! l)"
        by (simp add: ro_mxr_def sel accl sibl mux_one)
      have "hn (ro_mxl ?xs l) (ro_mxr ?xs l)
            = digest_repr (h_node (sibs ! l) (?acc ! l))"
        by (simp add: mxl mxr hn_correct)
      with step False accSl show ?thesis by simp
    qed
  qed

  have c5: "?xs ! ro_kb l * (?xs ! ro_kb l - 1) = 0" if l: "l < dd" for l
    unfolding enc_ro_kb[OF k l] by (rule kbit_bool)

  have accdd: "?acc ! dd = path_root (h_leaf leaf) key sibs"
  proof -
    have "?acc ! dd = last ?acc"
      by (simp add: last_conv_nth sl)
    then show ?thesis by (simp add: acc_list_last)
  qed

  have c3: "seg (ro_acc dd) W ?xs = seg ro_root W ?xs \<longleftrightarrow>
            path_root (h_leaf leaf) key sibs = root"
    using enc_ro_acc[OF k, of dd] enc_ro_root[OF k]
    by (simp add: dig_iff accdd)

  have c4: "seg (ro_acc 0) W ?xs = seg ro_vd W ?xs \<longleftrightarrow> vd = h_leaf leaf"
    using enc_ro_acc[OF k, of 0] enc_ro_vd[OF k]
    by (auto simp add: dig_iff)

  have c6: "?xs ! ro_lp * (?xs ! ro_lp - 2) = 0
            \<longleftrightarrow> (leaf = Empty \<or> leaf = Tombstone)"
    unfolding enc_ro_tag[OF k]
    by (simp add: leaf_tag_val_zero_or_two)

  show ?thesis
    unfolding cons_ro_def
    using c1 c2 c3 c4 c5 c6 by blast
qed

subsection \<open>Segment values of the Update encoding\<close>

lemma length_enc_up_core:
  "length (enc_up_core old new key sibs root root' vd) = up_width"
proof -
  have acc1: "length (concat (map (\<lambda>l. digest_repr (acc_list (h_leaf old) key sibs ! l))
                                  [0 ..< Suc dd])) = Suc dd * W"
    by (intro concat_map_uniform_length) simp
  have acc2: "length (concat (map (\<lambda>l. digest_repr (acc_list (h_leaf new) key sibs ! l))
                                  [0 ..< Suc dd])) = Suc dd * W"
    by (intro concat_map_uniform_length) simp
  have sib: "length (concat (map (\<lambda>l. digest_repr (sibs ! l)) [0 ..< dd])) = dd * W"
    by (intro concat_map_uniform_length) simp
  show ?thesis
    unfolding enc_up_core_def up_width_def up_vd_def up_root2_def up_root_def
    by (simp only: length_append acc1 acc2 sib length_map length_upt
                   digest_len leaf_len)
       (simp add: algebra_simps)
qed

lemma length_enc_up:
  "length (enc_up old new key sibs root root' vd) = ivlen KUpdate"
proof -
  have "length (enc_up_core old new key sibs root root' vd) \<le> ivlen KUpdate"
    using in_width_le_ivlen[of KUpdate] by (simp add: length_enc_up_core)
  then show ?thesis by (simp add: enc_up_def length_pad_to)
qed

lemma enc_up_segs:
  fixes old new :: "'v leaf_state" and key :: nat and sibs :: "'d list"
    and root root' vd :: 'd
  defines "xs \<equiv> enc_up old new key sibs root root' vd"
  shows enc_up_lp: "seg up_lp L xs = leaf_repr old"
    and enc_up_lp2: "seg up_lp2 L xs = leaf_repr new"
    and enc_up_acc:
      "\<And>l. l \<le> dd \<Longrightarrow> seg (up_acc l) W xs
                       = digest_repr (acc_list (h_leaf old) key sibs ! l)"
    and enc_up_acc2:
      "\<And>l. l \<le> dd \<Longrightarrow> seg (up_acc2 l) W xs
                       = digest_repr (acc_list (h_leaf new) key sibs ! l)"
    and enc_up_sib:
      "\<And>l. l < dd \<Longrightarrow> seg (up_sib l) W xs = digest_repr (sibs ! l)"
    and enc_up_kb: "\<And>l. l < dd \<Longrightarrow> xs ! up_kb l = kbit key l"
    and enc_up_root: "seg up_root W xs = digest_repr root"
    and enc_up_root2: "seg up_root2 W xs = digest_repr root'"
    and enc_up_vd: "seg up_vd W xs = digest_repr vd"
proof -
  let ?f1 = "\<lambda>l. digest_repr (acc_list (h_leaf old) key sibs ! l)"
  let ?f2 = "\<lambda>l. digest_repr (acc_list (h_leaf new) key sibs ! l)"
  let ?g = "\<lambda>l. digest_repr (sibs ! l)"
  let ?ACC1 = "concat (map ?f1 [0 ..< Suc dd])"
  let ?ACC2 = "concat (map ?f2 [0 ..< Suc dd])"
  let ?SIB = "concat (map ?g [0 ..< dd])"
  let ?KB = "map (kbit key) [0 ..< dd] :: 'f list"
  let ?core = "enc_up_core old new key sibs root root' vd"
  have core_eq: "?core = leaf_repr old @ leaf_repr new @ ?ACC1 @ ?ACC2 @ ?SIB @ ?KB
                         @ digest_repr root @ digest_repr root' @ digest_repr vd"
    by (simp add: enc_up_core_def)
  have lACC1: "length ?ACC1 = Suc dd * W"
    by (intro concat_map_uniform_length) simp
  have lACC2: "length ?ACC2 = Suc dd * W"
    by (intro concat_map_uniform_length) simp
  have lSIB: "length ?SIB = dd * W"
    by (intro concat_map_uniform_length) simp
  have lcore: "length ?core = up_width" by (rule length_enc_up_core)
  have xs_pad: "xs = pad_to (ivlen KUpdate) ?core" by (simp add: xs_def enc_up_def)
  have segP: "a + w \<le> up_width \<Longrightarrow> seg a w xs = seg a w ?core" for a w
    unfolding xs_pad by (rule seg_pad_to) (simp add: lcore)
  have nthP: "i < up_width \<Longrightarrow> xs ! i = ?core ! i" for i
    unfolding xs_pad by (rule pad_to_nth) (simp add: lcore)

  show "seg up_lp L xs = leaf_repr old"
    using segP[OF up_seg_bounds(1)]
    unfolding core_eq up_lp_def by (simp add: seg_def)

  show "seg up_lp2 L xs = leaf_repr new"
  proof -
    have c2: "?core = leaf_repr old @ leaf_repr new
                      @ (?ACC1 @ ?ACC2 @ ?SIB @ ?KB @ digest_repr root
                         @ digest_repr root' @ digest_repr vd)"
      unfolding core_eq by simp
    have "seg up_lp2 L ?core = leaf_repr new"
      unfolding c2 by (rule seg_at[of "leaf_repr old"]) (simp_all add: up_lp2_def)
    then show ?thesis using segP[OF up_seg_bounds(2)] by simp
  qed

  show "seg (up_acc l) W xs = ?f1 l" if l: "l \<le> dd" for l
  proof -
    have split: "?ACC1 = concat (map ?f1 [0 ..< l]) @ ?f1 l
                         @ concat (map ?f1 [Suc l ..< Suc dd])"
      by (rule concat_map_upt_split) (simp add: le_imp_less_Suc[OF l])
    have c2: "?core = (leaf_repr old @ leaf_repr new @ concat (map ?f1 [0 ..< l]))
                      @ ?f1 l
                      @ (concat (map ?f1 [Suc l ..< Suc dd]) @ ?ACC2 @ ?SIB @ ?KB
                         @ digest_repr root @ digest_repr root' @ digest_repr vd)"
      unfolding core_eq split by simp
    have lblk: "length (concat (map ?f1 [0 ..< l])) = l * W"
      by (intro concat_map_uniform_length) simp
    have lpre: "length (leaf_repr old @ leaf_repr new @ concat (map ?f1 [0 ..< l]))
                = up_acc l"
      by (simp add: lblk up_acc_def mult.commute)
    have "seg (up_acc l) W ?core = ?f1 l"
      unfolding c2 by (rule seg_at[OF lpre]) simp
    then show ?thesis using segP[OF up_seg_bounds(3)[OF l]] by simp
  qed

  show "seg (up_acc2 l) W xs = ?f2 l" if l: "l \<le> dd" for l
  proof -
    have split: "?ACC2 = concat (map ?f2 [0 ..< l]) @ ?f2 l
                         @ concat (map ?f2 [Suc l ..< Suc dd])"
      by (rule concat_map_upt_split) (simp add: le_imp_less_Suc[OF l])
    have c2: "?core = (leaf_repr old @ leaf_repr new @ ?ACC1 @ concat (map ?f2 [0 ..< l]))
                      @ ?f2 l
                      @ (concat (map ?f2 [Suc l ..< Suc dd]) @ ?SIB @ ?KB
                         @ digest_repr root @ digest_repr root' @ digest_repr vd)"
      unfolding core_eq split by simp
    have lblk: "length (concat (map ?f2 [0 ..< l])) = l * W"
      by (intro concat_map_uniform_length) simp
    have lpre: "length (leaf_repr old @ leaf_repr new @ ?ACC1 @ concat (map ?f2 [0 ..< l]))
                = up_acc2 l"
      unfolding up_acc2_def
      by (simp only: length_append lACC1 lblk leaf_len) (simp add: algebra_simps)
    have "seg (up_acc2 l) W ?core = ?f2 l"
      unfolding c2 by (rule seg_at[OF lpre]) simp
    then show ?thesis using segP[OF up_seg_bounds(4)[OF l]] by simp
  qed

  show "seg (up_sib l) W xs = ?g l" if l: "l < dd" for l
  proof -
    have split: "?SIB = concat (map ?g [0 ..< l]) @ ?g l @ concat (map ?g [Suc l ..< dd])"
      by (rule concat_map_upt_split) (rule l)
    have c2: "?core = (leaf_repr old @ leaf_repr new @ ?ACC1 @ ?ACC2
                       @ concat (map ?g [0 ..< l]))
                      @ ?g l
                      @ (concat (map ?g [Suc l ..< dd]) @ ?KB
                         @ digest_repr root @ digest_repr root' @ digest_repr vd)"
      unfolding core_eq split by simp
    have lblk: "length (concat (map ?g [0 ..< l])) = l * W"
      by (intro concat_map_uniform_length) simp
    have lpre: "length (leaf_repr old @ leaf_repr new @ ?ACC1 @ ?ACC2
                        @ concat (map ?g [0 ..< l])) = up_sib l"
      unfolding up_sib_def
      by (simp only: length_append lACC1 lACC2 lblk leaf_len)
         (simp add: algebra_simps)
    have "seg (up_sib l) W ?core = ?g l"
      unfolding c2 by (rule seg_at[OF lpre]) simp
    then show ?thesis using segP[OF up_seg_bounds(5)[OF l]] by simp
  qed

  show "xs ! up_kb l = kbit key l" if l: "l < dd" for l
  proof -
    have c2: "?core = (leaf_repr old @ leaf_repr new @ ?ACC1 @ ?ACC2 @ ?SIB) @ ?KB
                      @ (digest_repr root @ digest_repr root' @ digest_repr vd)"
      unfolding core_eq by simp
    have lpre: "length (leaf_repr old @ leaf_repr new @ ?ACC1 @ ?ACC2 @ ?SIB)
                = 2 * L + W * (3 * dd + 2)"
      by (simp only: length_append lACC1 lACC2 lSIB leaf_len)
         (simp add: algebra_simps)
    have "?core ! (2 * L + W * (3 * dd + 2) + l) = ?KB ! l"
      unfolding c2 by (rule nth_at[OF lpre]) (simp add: l)
    then have "?core ! up_kb l = kbit key l"
      using l by (simp add: up_kb_def)
    then show ?thesis using nthP[OF up_seg_bounds(6)[OF l]] by simp
  qed

  show "seg up_root W xs = digest_repr root"
  proof -
    have c2: "?core = (leaf_repr old @ leaf_repr new @ ?ACC1 @ ?ACC2 @ ?SIB @ ?KB)
                      @ digest_repr root @ (digest_repr root' @ digest_repr vd)"
      unfolding core_eq by simp
    have lpre: "length (leaf_repr old @ leaf_repr new @ ?ACC1 @ ?ACC2 @ ?SIB @ ?KB)
                = up_root"
      unfolding up_root_def
      by (simp only: length_append lACC1 lACC2 lSIB leaf_len length_map length_upt)
         (simp add: algebra_simps)
    have "seg up_root W ?core = digest_repr root"
      unfolding c2 by (rule seg_at[OF lpre]) simp
    then show ?thesis using segP[OF up_seg_bounds(7)] by simp
  qed

  show "seg up_root2 W xs = digest_repr root'"
  proof -
    have c2: "?core = (leaf_repr old @ leaf_repr new @ ?ACC1 @ ?ACC2 @ ?SIB @ ?KB
                       @ digest_repr root)
                      @ digest_repr root' @ digest_repr vd"
      unfolding core_eq by simp
    have lpre: "length (leaf_repr old @ leaf_repr new @ ?ACC1 @ ?ACC2 @ ?SIB @ ?KB
                        @ digest_repr root) = up_root2"
      unfolding up_root2_def up_root_def
      by (simp only: length_append lACC1 lACC2 lSIB leaf_len length_map length_upt
                     digest_len)
         (simp add: algebra_simps)
    have "seg up_root2 W ?core = digest_repr root'"
      unfolding c2 by (rule seg_at[OF lpre]) simp
    then show ?thesis using segP[OF up_seg_bounds(8)] by simp
  qed

  show "seg up_vd W xs = digest_repr vd"
  proof -
    have c2: "?core = (leaf_repr old @ leaf_repr new @ ?ACC1 @ ?ACC2 @ ?SIB @ ?KB
                       @ digest_repr root @ digest_repr root')
                      @ digest_repr vd @ []"
      unfolding core_eq by simp
    have lpre: "length (leaf_repr old @ leaf_repr new @ ?ACC1 @ ?ACC2 @ ?SIB @ ?KB
                        @ digest_repr root @ digest_repr root') = up_vd"
      unfolding up_vd_def up_root2_def up_root_def
      by (simp only: length_append lACC1 lACC2 lSIB leaf_len length_map length_upt
                     digest_len)
         (simp add: algebra_simps)
    have "seg up_vd W ?core = digest_repr vd"
      unfolding c2 by (rule seg_at[OF lpre]) simp
    then show ?thesis using segP[OF up_seg_bounds(9)] by simp
  qed
qed

subsection \<open>The Update constraint conjunction on the honest encoding\<close>

text \<open>One compression-chain step holds by construction (either chain).\<close>

lemma up_chain_holds:
  assumes accF: "\<And>j. j \<le> dd \<Longrightarrow> seg (accoff j) W xs
                                 = digest_repr (acc_list a0 key sibs ! j)"
      and sibF: "seg (up_sib l) W xs = digest_repr (sibs ! l)"
      and kbF: "xs ! up_kb l = kbit key l"
      and sl: "length sibs = dd" and l: "l < dd"
  shows "hn (up_mxl xs accoff l) (up_mxr xs accoff l) = seg (accoff (Suc l)) W xs"
proof -
  let ?acc = "acc_list a0 key sibs"
  have accl: "seg (accoff l) W xs = digest_repr (?acc ! l)"
    using accF l by simp
  have accSl: "seg (accoff (Suc l)) W xs = digest_repr (?acc ! Suc l)"
    using accF l by (simp add: Suc_le_eq)
  have step: "?acc ! Suc l =
                (if (key div 2 ^ l) mod 2 = 0
                 then h_node (?acc ! l) (sibs ! l)
                 else h_node (sibs ! l) (?acc ! l))"
    by (rule acc_list_step) (simp add: sl l)
  show ?thesis
  proof (cases "(key div 2 ^ l) mod 2 = 0")
    case True
    have sel: "xs ! up_kb l = 0"
      using True by (simp add: kbF kbit_def)
    have mxl: "up_mxl xs accoff l = digest_repr (?acc ! l)"
      by (simp add: up_mxl_def sel accl sibF mux_zero)
    have mxr: "up_mxr xs accoff l = digest_repr (sibs ! l)"
      by (simp add: up_mxr_def sel accl sibF mux_zero)
    have "hn (up_mxl xs accoff l) (up_mxr xs accoff l)
          = digest_repr (h_node (?acc ! l) (sibs ! l))"
      by (simp add: mxl mxr hn_correct)
    with step True accSl show ?thesis by simp
  next
    case False
    have lt2: "(key div 2 ^ l) mod 2 < 2" by simp
    with False have m1: "(key div 2 ^ l) mod 2 = 1" by arith
    have sel: "xs ! up_kb l = 1"
      by (simp add: kbF kbit_def m1)
    have mxl: "up_mxl xs accoff l = digest_repr (sibs ! l)"
      by (simp add: up_mxl_def sel accl sibF mux_one)
    have mxr: "up_mxr xs accoff l = digest_repr (?acc ! l)"
      by (simp add: up_mxr_def sel accl sibF mux_one)
    have "hn (up_mxl xs accoff l) (up_mxr xs accoff l)
          = digest_repr (h_node (sibs ! l) (?acc ! l))"
      by (simp add: mxl mxr hn_correct)
    with step False accSl show ?thesis by simp
  qed
qed

lemma cons_up_enc:
  assumes sl: "length sibs = dd"
  shows "cons_up (enc_up old new key sibs root root' vd) \<longleftrightarrow>
           (path_root (h_leaf old) key sibs = root \<and>
            path_root (h_leaf new) key sibs = root' \<and> vd = h_leaf new)"
proof -
  let ?xs = "enc_up old new key sibs root root' vd"
  let ?acc1 = "acc_list (h_leaf old) key sibs"
  let ?acc2 = "acc_list (h_leaf new) key sibs"
  have dig_iff: "digest_repr x = digest_repr y \<longleftrightarrow> x = y" for x y
    using digest_inj by auto

  have c1: "hl (seg up_lp L ?xs) = seg (up_acc 0) W ?xs"
    using enc_up_lp enc_up_acc[of 0] by (simp add: hl_correct)
  have c1': "hl (seg up_lp2 L ?xs) = seg (up_acc2 0) W ?xs"
    using enc_up_lp2 enc_up_acc2[of 0] by (simp add: hl_correct)

  have c2: "hn (up_mxl ?xs up_acc l) (up_mxr ?xs up_acc l)
            = seg (up_acc (Suc l)) W ?xs" if l: "l < dd" for l
    by (rule up_chain_holds[OF enc_up_acc enc_up_sib[OF l] enc_up_kb[OF l] sl l])
  have c2': "hn (up_mxl ?xs up_acc2 l) (up_mxr ?xs up_acc2 l)
             = seg (up_acc2 (Suc l)) W ?xs" if l: "l < dd" for l
    by (rule up_chain_holds[OF enc_up_acc2 enc_up_sib[OF l] enc_up_kb[OF l] sl l])

  have c8: "?xs ! up_kb l * (?xs ! up_kb l - 1) = 0" if l: "l < dd" for l
    unfolding enc_up_kb[OF l] by (rule kbit_bool)

  have accdd1: "?acc1 ! dd = path_root (h_leaf old) key sibs"
  proof -
    have "?acc1 ! dd = last ?acc1" by (simp add: last_conv_nth sl)
    then show ?thesis by (simp add: acc_list_last)
  qed
  have accdd2: "?acc2 ! dd = path_root (h_leaf new) key sibs"
  proof -
    have "?acc2 ! dd = last ?acc2" by (simp add: last_conv_nth sl)
    then show ?thesis by (simp add: acc_list_last)
  qed

  have c5: "seg (up_acc dd) W ?xs = seg up_root W ?xs \<longleftrightarrow>
            path_root (h_leaf old) key sibs = root"
    using enc_up_acc[of dd] enc_up_root by (simp add: dig_iff accdd1)
  have c6: "seg (up_acc2 dd) W ?xs = seg up_root2 W ?xs \<longleftrightarrow>
            path_root (h_leaf new) key sibs = root'"
    using enc_up_acc2[of dd] enc_up_root2 by (simp add: dig_iff accdd2)
  have c7: "seg (up_acc2 0) W ?xs = seg up_vd W ?xs \<longleftrightarrow> vd = h_leaf new"
    using enc_up_acc2[of 0] enc_up_vd by (auto simp add: dig_iff)

  show ?thesis
    unfolding cons_up_def
    using c1 c1' c2 c2' c5 c6 c7 c8 by blast
qed

end

section \<open>Theorem A: the verifier model and the compilation soundness\<close>

text \<open>
  The complete verifier = the facade public-input checks (Rust:
  \<open>verify_sync_op\<close>'s native guards) plus circuit acceptance on the honest
  witness encoding.  The value-digest canonicity (\<open>vd_ok\<close>) is derived
  from CANONICAL/public values only, never the private witness leaf (the
  fix for a false non-membership acceptance), and the two facade echoes
  mirror the literal code.

  Theorem A then holds DETERMINISTICALLY (no collision resistance):

  \<^item> soundness: an accepted (vd, w) yields \<open>smt_valid\<close> for the CANONICAL
    witness - identical to w except that Membership replaces the witness
    leaf by \<open>Occupied v\<close>.  (The witness leaf reaches the circuit only
    through its \<open>h_leaf\<close> image, so the semantic clauses transport along
    \<open>h_leaf leaf = vd = h_leaf (Occupied v)\<close>; pinning the witness leaf
    ITSELF is exactly an \<open>h_leaf\<close> injectivity question, which lemma (b)
    reduces to Poseidon2 sponge collisions - system-level territory,
    property boundary.)
  \<^item> completeness: a semantically valid witness is accepted with the
    canonical value digest.
  \<^item> packaging: acceptance for SOME (vd, w) iff \<open>smt_valid\<close> for SOME w.
\<close>

context compiler_model
begin

definition vd_ok :: "'v smt_op \<Rightarrow> 'd \<Rightarrow> bool" where
  "vd_ok op vd = (case op of
     Membership k v \<Rightarrow> vd = h_leaf (Occupied v)
   | NonMembership k \<Rightarrow> vd = h_leaf Empty \<or> vd = h_leaf Tombstone
   | Update k old new \<Rightarrow> vd = h_leaf new)"

definition pub_ok :: "'v smt_op \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> bool" where
  "pub_ok op root root' vd \<longleftrightarrow>
     (kind_of op \<noteq> KUpdate \<longrightarrow> root' = root) \<and>
     op_key op < 2 ^ dd \<and> vd_ok op vd"

definition echo_ok :: "'v smt_op \<Rightarrow> ('v leaf_state \<times> 'd list) \<Rightarrow> bool" where
  "echo_ok op w = (case op of
     Membership k v \<Rightarrow> True
   | NonMembership k \<Rightarrow> fst w = Empty \<or> fst w = Tombstone
   | Update k old new \<Rightarrow> fst w = old)"

definition verifier_accept :: "'v smt_op \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> ('v leaf_state \<times> 'd list) \<Rightarrow> bool" where
  "verifier_accept op root root' vd w \<longleftrightarrow>
     pub_ok op root root' vd \<and> length (snd w) = dd \<and> echo_ok op w \<and>
     circuit_accept (compile (kind_of op)) (encode_witness op root root' vd w)"

text \<open>The canonical witness: Membership pins the leaf to the public payload.\<close>

definition canon_witness :: "'v smt_op \<Rightarrow> ('v leaf_state \<times> 'd list) \<Rightarrow> ('v leaf_state \<times> 'd list)" where
  "canon_witness op w = (case op of
     Membership k v \<Rightarrow> (Occupied v, snd w)
   | _ \<Rightarrow> w)"

text \<open>The canonical value digest for a semantically valid witness.\<close>

definition wit_vd :: "'v smt_op \<Rightarrow> ('v leaf_state \<times> 'd list) \<Rightarrow> 'd" where
  "wit_vd op w = (case op of
     Membership k v \<Rightarrow> h_leaf (Occupied v)
   | NonMembership k \<Rightarrow> h_leaf (fst w)
   | Update k old new \<Rightarrow> h_leaf new)"

theorem theorem_A_soundness:
  assumes acc: "verifier_accept op root root' vd w"
  shows "smt_valid op root root' (canon_witness op w)"
proof (cases op)
  case (Membership k v)
  obtain leaf sibs where w: "w = (leaf, sibs)" by (cases w)
  from acc have pub: "pub_ok op root root' vd"
    and lsib: "length sibs = dd"
    and circ: "circuit_accept (compile KMembership)
                 (enc_ro KMembership leaf k sibs root vd)"
    by (auto simp: verifier_accept_def Membership w encode_witness_def)
  have "cons_ro KMembership (enc_ro KMembership leaf k sibs root vd)"
    using A_i_ro[of KMembership] circ by (simp add: length_enc_ro)
  then have path: "path_root (h_leaf leaf) k sibs = root"
    and vdl: "vd = h_leaf leaf"
    using cons_ro_enc[OF _ lsib] by auto
  from pub have root_eq: "root' = root" and key_rng: "k < 2 ^ dd"
    and vdc: "vd = h_leaf (Occupied v)"
    by (auto simp: pub_ok_def vd_ok_def Membership)
  have "path_root (h_leaf (Occupied v)) k sibs = root"
    using path vdl vdc by simp
  then have "path_ok (Occupied v) k sibs root"
    using lsib key_rng by (simp add: path_ok_def)
  then show ?thesis
    by (simp add: Membership w canon_witness_def root_eq)
next
  case (NonMembership k)
  obtain leaf sibs where w: "w = (leaf, sibs)" by (cases w)
  from acc have pub: "pub_ok op root root' vd"
    and lsib: "length sibs = dd"
    and circ: "circuit_accept (compile KNonMembership)
                 (enc_ro KNonMembership leaf k sibs root vd)"
    by (auto simp: verifier_accept_def NonMembership w encode_witness_def)
  have "cons_ro KNonMembership (enc_ro KNonMembership leaf k sibs root vd)"
    using A_i_ro[of KNonMembership] circ by (simp add: length_enc_ro)
  then have path: "path_root (h_leaf leaf) k sibs = root"
    and tags: "leaf = Empty \<or> leaf = Tombstone"
    using cons_ro_enc[OF _ lsib] by auto
  from pub have root_eq: "root' = root" and key_rng: "k < 2 ^ dd"
    by (auto simp: pub_ok_def NonMembership)
  have "path_ok leaf k sibs root"
    using path lsib key_rng by (simp add: path_ok_def)
  then show ?thesis
    by (simp add: NonMembership w canon_witness_def root_eq tags)
next
  case (Update k old new)
  obtain leaf sibs where w: "w = (leaf, sibs)" by (cases w)
  from acc have pub: "pub_ok op root root' vd"
    and lsib: "length sibs = dd"
    and echo: "leaf = old"
    and circ: "circuit_accept (compile KUpdate)
                 (enc_up old new k sibs root root' vd)"
    by (auto simp: verifier_accept_def Update w encode_witness_def echo_ok_def)
  have "cons_up (enc_up old new k sibs root root' vd)"
    using A_i_up circ by (simp add: length_enc_up)
  then have path1: "path_root (h_leaf old) k sibs = root"
    and path2: "path_root (h_leaf new) k sibs = root'"
    using cons_up_enc[OF lsib] by auto
  from pub have key_rng: "k < 2 ^ dd" by (simp add: pub_ok_def Update)
  have "path_ok old k sibs root" and "path_ok new k sibs root'"
    using path1 path2 lsib key_rng by (simp_all add: path_ok_def)
  then show ?thesis
    by (simp add: Update w canon_witness_def echo)
qed

theorem theorem_A_completeness:
  assumes valid: "smt_valid op root root' w"
  shows "verifier_accept op root root' (wit_vd op w) w"
proof (cases op)
  case (Membership k v)
  obtain leaf sibs where w: "w = (leaf, sibs)" by (cases w)
  from valid have root_eq: "root' = root" and leaf_eq: "leaf = Occupied v"
    and pok: "path_ok leaf k sibs root"
    by (auto simp: Membership w)
  from pok have lsib: "length sibs = dd" and key_rng: "k < 2 ^ dd"
    and path: "path_root (h_leaf leaf) k sibs = root"
    by (auto simp: path_ok_def)
  have vd: "wit_vd op w = h_leaf (Occupied v)"
    by (simp add: wit_vd_def Membership)
  have "cons_ro KMembership (enc_ro KMembership leaf k sibs root (wit_vd op w))"
    using cons_ro_enc[OF _ lsib] path leaf_eq vd by auto
  then have "circuit_accept (compile KMembership)
               (enc_ro KMembership leaf k sibs root (wit_vd op w))"
    using A_i_ro[of KMembership] by (simp add: length_enc_ro)
  then show ?thesis
    by (simp add: verifier_accept_def pub_ok_def vd_ok_def echo_ok_def
                  encode_witness_def wit_vd_def Membership w root_eq key_rng lsib)
next
  case (NonMembership k)
  obtain leaf sibs where w: "w = (leaf, sibs)" by (cases w)
  from valid have root_eq: "root' = root" and tags: "leaf = Empty \<or> leaf = Tombstone"
    and pok: "path_ok leaf k sibs root"
    by (auto simp: NonMembership w)
  from pok have lsib: "length sibs = dd" and key_rng: "k < 2 ^ dd"
    and path: "path_root (h_leaf leaf) k sibs = root"
    by (auto simp: path_ok_def)
  have vd: "wit_vd op w = h_leaf leaf"
    by (simp add: wit_vd_def NonMembership w)
  have "cons_ro KNonMembership (enc_ro KNonMembership leaf k sibs root (wit_vd op w))"
    using cons_ro_enc[OF _ lsib] path tags vd by auto
  then have "circuit_accept (compile KNonMembership)
               (enc_ro KNonMembership leaf k sibs root (wit_vd op w))"
    using A_i_ro[of KNonMembership] by (simp add: length_enc_ro)
  then show ?thesis
    using tags
    by (auto simp: verifier_accept_def pub_ok_def vd_ok_def echo_ok_def
                   encode_witness_def wit_vd_def NonMembership w root_eq key_rng lsib)
next
  case (Update k old new)
  obtain leaf sibs where w: "w = (leaf, sibs)" by (cases w)
  from valid have leaf_eq: "leaf = old"
    and pok1: "path_ok old k sibs root" and pok2: "path_ok new k sibs root'"
    by (auto simp: Update w)
  from pok1 have lsib: "length sibs = dd" and key_rng: "k < 2 ^ dd"
    and path1: "path_root (h_leaf old) k sibs = root"
    by (auto simp: path_ok_def)
  from pok2 have path2: "path_root (h_leaf new) k sibs = root'"
    by (auto simp: path_ok_def)
  have vd: "wit_vd op w = h_leaf new"
    by (simp add: wit_vd_def Update)
  have "cons_up (enc_up old new k sibs root root' (wit_vd op w))"
    using cons_up_enc[OF lsib] path1 path2 vd by auto
  then have "circuit_accept (compile KUpdate)
               (enc_up old new k sibs root root' (wit_vd op w))"
    using A_i_up by (simp add: length_enc_up)
  then show ?thesis
    by (simp add: verifier_accept_def pub_ok_def vd_ok_def echo_ok_def
                  encode_witness_def wit_vd_def Update w key_rng lsib leaf_eq)
qed

text \<open>
  Theorem A, packaged: the verifier accepts SOME (value digest, witness)
  for (op, root, root') iff the operation is semantically valid between
  those roots for SOME witness.  This existential biconditional is the
  exact form the composition (Theorem C) consumes.
\<close>

theorem theorem_A_compilation_soundness:
  "(\<exists>vd w. verifier_accept op root root' vd w)
   \<longleftrightarrow> (\<exists>w. smt_valid op root root' w)"
proof
  assume "\<exists>vd w. verifier_accept op root root' vd w"
  then obtain vd w where "verifier_accept op root root' vd w" by blast
  then have "smt_valid op root root' (canon_witness op w)"
    by (rule theorem_A_soundness)
  then show "\<exists>w. smt_valid op root root' w" by blast
next
  assume "\<exists>w. smt_valid op root root' w"
  then obtain w where "smt_valid op root root' w" by blast
  then have "verifier_accept op root root' (wit_vd op w) w"
    by (rule theorem_A_completeness)
  then show "\<exists>vd w. verifier_accept op root root' vd w" by blast
qed

end

end