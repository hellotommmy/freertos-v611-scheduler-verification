theory List_V611_Raw_R5_Cycle
  imports "EAL6_FreeRTOS_V611_List_Raw_R5_Interface.List_V611_Raw_R5_Interface"
begin

text \<open>
  General finite-cycle bricks for the raw representation.  The proofs work
  for an arbitrary list address and arbitrary ring length; they do not open a
  generated C body.  This is the sequence/reachability layer required before
  a general-N insertion or removal VCG is attempted.
\<close>

definition raw_cycle_nodes ::
  "xLIST_C ptr \<Rightarrow> raw_node_id list \<Rightarrow> raw_node_id list"
where
  "raw_cycle_nodes lp rs = raw_end_item lp # rs"

definition raw_cycle_targets ::
  "xLIST_C ptr \<Rightarrow> raw_node_id list \<Rightarrow> raw_node_id list"
where
  "raw_cycle_targets lp rs = rs @ [raw_end_item lp]"

lemma raw_cycle_nodes_length[simp]:
  "length (raw_cycle_nodes lp rs) = Suc (length rs)"
  by (simp add: raw_cycle_nodes_def)

lemma raw_cycle_targets_length[simp]:
  "length (raw_cycle_targets lp rs) = Suc (length rs)"
  by (simp add: raw_cycle_targets_def)

lemma raw_edge_pairs_as_cycles:
  "raw_edge_pairs lp rs =
   zip (raw_cycle_nodes lp rs) (raw_cycle_targets lp rs)"
  by (simp add: raw_edge_pairs_def raw_cycle_nodes_def
      raw_cycle_targets_def)

lemma raw_ring_links_nth_edge:
  assumes links: "raw_ring_links h lp rs"
    and bound: "i < Suc (length rs)"
  shows
    "raw_next_at h lp (raw_cycle_nodes lp rs ! i) =
       raw_cycle_targets lp rs ! i \<and>
     raw_prev_at h lp (raw_cycle_targets lp rs ! i) =
       raw_cycle_nodes lp rs ! i"
proof -
  have all_edges:
    "\<forall>pq \<in> set (raw_edge_pairs lp rs).
       (case pq of (p,q) \<Rightarrow>
          raw_next_at h lp p = q \<and> raw_prev_at h lp q = p)"
    using links by (simp add: raw_ring_links_def list_all_iff)
  have pair_bound: "i < length (raw_edge_pairs lp rs)"
    using bound by simp
  have pair_mem:
    "raw_edge_pairs lp rs ! i \<in> set (raw_edge_pairs lp rs)"
    by (rule nth_mem[OF pair_bound])
  have pair_nth:
    "raw_edge_pairs lp rs ! i =
      (raw_cycle_nodes lp rs ! i, raw_cycle_targets lp rs ! i)"
    unfolding raw_edge_pairs_as_cycles
    using bound by simp
  have edge_property:
    "(case raw_edge_pairs lp rs ! i of (p,q) \<Rightarrow>
       raw_next_at h lp p = q \<and> raw_prev_at h lp q = p)"
  proof (rule all_edges[rule_format])
    show "raw_edge_pairs lp rs ! i \<in> set (raw_edge_pairs lp rs)"
      by (rule pair_mem)
  qed
  show ?thesis
    using edge_property by (simp add: pair_nth)
qed

corollary raw_ring_links_nth_next:
  "raw_ring_links h lp rs \<Longrightarrow> i < Suc (length rs) \<Longrightarrow>
   raw_next_at h lp (raw_cycle_nodes lp rs ! i) =
     raw_cycle_targets lp rs ! i"
  using raw_ring_links_nth_edge by blast

corollary raw_ring_links_nth_previous:
  "raw_ring_links h lp rs \<Longrightarrow> i < Suc (length rs) \<Longrightarrow>
   raw_prev_at h lp (raw_cycle_targets lp rs ! i) =
     raw_cycle_nodes lp rs ! i"
  using raw_ring_links_nth_edge by blast

lemma raw_cycle_target_before_last:
  assumes "i < length rs"
  shows "raw_cycle_targets lp rs ! i = raw_cycle_nodes lp rs ! Suc i"
  using assms
  by (simp add: raw_cycle_targets_def raw_cycle_nodes_def nth_append)

lemma raw_cycle_target_last[simp]:
  "raw_cycle_targets lp rs ! length rs = raw_end_item lp"
  by (simp add: raw_cycle_targets_def)

lemma raw_next_power_nth:
  assumes links: "raw_ring_links h lp rs"
    and bound: "i \<le> length rs"
  shows
    "(raw_next_at h lp ^^ i) (raw_end_item lp) =
       raw_cycle_nodes lp rs ! i"
  using bound
proof (induction i)
  case 0
  then show ?case by (simp add: raw_cycle_nodes_def)
next
  case (Suc i)
  have i_bound: "i \<le> length rs"
    using Suc.prems by simp
  have i_strict: "i < length rs"
    using Suc.prems by simp
  have edge:
    "raw_next_at h lp (raw_cycle_nodes lp rs ! i) =
       raw_cycle_targets lp rs ! i"
    using raw_ring_links_nth_next[OF links] i_bound by simp
  show ?case
    using Suc.IH[OF i_bound] edge
      raw_cycle_target_before_last[OF i_strict, where lp=lp]
    by simp
qed

lemma raw_next_power_return_after_cycle:
  assumes links: "raw_ring_links h lp rs"
  shows
    "(raw_next_at h lp ^^ Suc (length rs)) (raw_end_item lp) =
       raw_end_item lp"
proof -
  have path:
    "(raw_next_at h lp ^^ length rs) (raw_end_item lp) =
       raw_cycle_nodes lp rs ! length rs"
    by (rule raw_next_power_nth[OF links order_refl])
  have edge:
    "raw_next_at h lp (raw_cycle_nodes lp rs ! length rs) =
       raw_cycle_targets lp rs ! length rs"
    by (rule raw_ring_links_nth_next[OF links], simp)
  show ?thesis
    using path edge by simp
qed

lemma raw_next_power_no_early_return:
  assumes links: "raw_ring_links h lp rs"
    and distinct: "distinct (raw_cycle_nodes lp rs)"
    and positive: "0 < i"
    and early: "i < Suc (length rs)"
  shows
    "(raw_next_at h lp ^^ i) (raw_end_item lp) \<noteq> raw_end_item lp"
proof -
  have path:
    "(raw_next_at h lp ^^ i) (raw_end_item lp) =
       raw_cycle_nodes lp rs ! i"
    by (rule raw_next_power_nth[OF links], use early in simp)
  have zero: "raw_cycle_nodes lp rs ! 0 = raw_end_item lp"
    by (simp add: raw_cycle_nodes_def)
  have neq: "raw_cycle_nodes lp rs ! i \<noteq> raw_cycle_nodes lp rs ! 0"
    using distinct positive early
    by (auto simp: distinct_conv_nth)
  show ?thesis using path zero neq by simp
qed

lemma raw_next_power_injective_before_return:
  assumes links: "raw_ring_links h lp rs"
    and distinct: "distinct (raw_cycle_nodes lp rs)"
    and i_bound: "i < Suc (length rs)"
    and j_bound: "j < Suc (length rs)"
  shows
    "((raw_next_at h lp ^^ i) (raw_end_item lp) =
      (raw_next_at h lp ^^ j) (raw_end_item lp)) \<longleftrightarrow> i = j"
proof -
  have path_i:
    "(raw_next_at h lp ^^ i) (raw_end_item lp) =
       raw_cycle_nodes lp rs ! i"
    by (rule raw_next_power_nth[OF links], use i_bound in simp)
  have path_j:
    "(raw_next_at h lp ^^ j) (raw_end_item lp) =
       raw_cycle_nodes lp rs ! j"
    by (rule raw_next_power_nth[OF links], use j_bound in simp)
  show ?thesis
    using distinct i_bound j_bound path_i path_j
    by (auto simp: distinct_conv_nth)
qed

lemma raw_next_power_reachable_exact:
  assumes links: "raw_ring_links h lp rs"
  shows
    "{p. \<exists>i < Suc (length rs).
       p = (raw_next_at h lp ^^ i) (raw_end_item lp)} =
     set (raw_cycle_nodes lp rs)"
proof (rule set_eqI)
  fix p
  show
    "p \<in> {p. \<exists>i < Suc (length rs).
       p = (raw_next_at h lp ^^ i) (raw_end_item lp)} \<longleftrightarrow>
     p \<in> set (raw_cycle_nodes lp rs)"
  proof
    assume "p \<in> {p. \<exists>i < Suc (length rs).
      p = (raw_next_at h lp ^^ i) (raw_end_item lp)}"
    then obtain i where bound: "i < Suc (length rs)" and
      p: "p = (raw_next_at h lp ^^ i) (raw_end_item lp)"
      by blast
    have path:
      "(raw_next_at h lp ^^ i) (raw_end_item lp) =
        raw_cycle_nodes lp rs ! i"
      by (rule raw_next_power_nth[OF links], use bound in simp)
    show "p \<in> set (raw_cycle_nodes lp rs)"
      using p path bound by (auto intro: nth_mem)
  next
    assume member: "p \<in> set (raw_cycle_nodes lp rs)"
    then obtain i where bound: "i < length (raw_cycle_nodes lp rs)" and
      p: "p = raw_cycle_nodes lp rs ! i"
      by (auto simp: in_set_conv_nth)
    have path:
      "(raw_next_at h lp ^^ i) (raw_end_item lp) =
        raw_cycle_nodes lp rs ! i"
      by (rule raw_next_power_nth[OF links], use bound in simp)
    show "p \<in> {p. \<exists>i < Suc (length rs).
      p = (raw_next_at h lp ^^ i) (raw_end_item lp)}"
      using bound p path by auto
  qed
qed

corollary raw_xlist_rel_first_return_and_reachability:
  assumes rel: "raw_xlist_rel h lp xs"
  shows
    "(raw_next_at h lp ^^ Suc (length (ring xs))) (raw_end_item lp) =
       raw_end_item lp \<and>
     (\<forall>i. 0 < i \<and> i < Suc (length (ring xs)) \<longrightarrow>
       (raw_next_at h lp ^^ i) (raw_end_item lp) \<noteq> raw_end_item lp) \<and>
     {p. \<exists>i < Suc (length (ring xs)).
       p = (raw_next_at h lp ^^ i) (raw_end_item lp)} =
       insert (raw_end_item lp) (set (ring xs))"
proof -
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have distinct: "distinct (raw_cycle_nodes lp (ring xs))"
    using raw_xlist_rel_distinct_cycle_nodes[OF rel]
    by (simp add: raw_cycle_nodes_def)
  show ?thesis
    using raw_next_power_return_after_cycle[OF links]
      raw_next_power_no_early_return[OF links distinct]
      raw_next_power_reachable_exact[OF links]
    by (auto simp: raw_cycle_nodes_def)
qed

end
