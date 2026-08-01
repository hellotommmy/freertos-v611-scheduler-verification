theory List_V611_Raw_R6_Remove_Topology_Effect
  imports "EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Source_Effects.List_V611_Raw_R6_Remove_Source_Effects"
begin

text \<open>
  General-N removal topology, separated from count and cursor metadata.
  The two link writes are discharged by the alias-safe unlink projection.
  The conditional index write, the removed item's container clear, and the
  final count write are then framed against every observation in the
  shortened ring before reopening the generated source monad.
\<close>

lemma raw_xlist_layout_remove1:
  assumes layout: "raw_xlist_layout lp rs"
  shows "raw_xlist_layout lp (remove1 p rs)"
  by (rule raw_xlist_layout_subset[OF layout set_remove1_subset])

lemma raw_distinct_member_notin_remove1:
  assumes distinct: "distinct rs"
    and member: "p \<in> set rs"
  shows "p \<notin> set (remove1 p rs)"
  using distinct member
proof (induction rs)
  case Nil
  then show ?case by simp
next
  case (Cons a rs)
  show ?case
  proof (cases "a = p")
    case True
    then show ?thesis using Cons.prems by simp
  next
    case False
    have tail_distinct: "distinct rs" and tail_member: "p \<in> set rs"
      using Cons.prems False by auto
    have "p \<notin> set (remove1 p rs)"
      by (rule Cons.IH[OF tail_distinct tail_member])
    then show ?thesis using False by simp
  qed
qed

lemma raw_list_update_preserves_disjoint_item:
  assumes disjoint:
    "raw_item_region q \<inter> raw_list_region lp = {}"
  shows
    "h_val (heap_update lp (v :: xLIST_C) h) q = h_val h q"
proof -
  have byte_disjoint:
    "{ptr_val lp..+
       length (to_bytes v
         (heap_list h (size_of TYPE(xLIST_C)) (ptr_val lp)))} \<inter>
     {ptr_val q..+size_of TYPE(xLIST_ITEM_C)} = {}"
    using disjoint
    by (simp add: raw_list_region_def raw_item_region_def Int_commute)
  have heap_lists_same:
    "heap_list
       (heap_update_list (ptr_val lp)
         (to_bytes v
           (heap_list h (size_of TYPE(xLIST_C)) (ptr_val lp))) h)
       (size_of TYPE(xLIST_ITEM_C)) (ptr_val q) =
     heap_list h (size_of TYPE(xLIST_ITEM_C)) (ptr_val q)"
    by (rule heap_list_update_disjoint_same[OF byte_disjoint])
  show ?thesis
    unfolding h_val_def heap_update_def
    using heap_lists_same by simp
qed

lemma raw_cycle_observations_survive_list_update:
  assumes layout: "raw_xlist_layout lp rs"
    and member: "u \<in> insert (raw_end_item lp) (set rs)"
    and end_same: "xListEnd_C v = xListEnd_C (h_val h lp)"
  shows
    "raw_next_at (heap_update lp (v :: xLIST_C) h) lp u =
       raw_next_at h lp u \<and>
     raw_prev_at (heap_update lp v h) lp u = raw_prev_at h lp u"
proof (cases "u = raw_end_item lp")
  case True
  have guard: "c_guard lp"
    using layout by (simp add: raw_xlist_layout_def)
  have list_same: "h_val (heap_update lp v h) lp = v"
    using guard by (simp add: h_val_heap_update)
  show ?thesis
    using True list_same end_same
    by (simp add: raw_next_at_def raw_prev_at_def)
next
  case False
  have u_real: "u \<in> set rs"
    using member False by simp
  have disjoint:
    "raw_item_region u \<inter> raw_list_region lp = {}"
    using layout u_real by (auto simp: raw_xlist_layout_def)
  have item_same: "h_val (heap_update lp v h) u = h_val h u"
    by (rule raw_list_update_preserves_disjoint_item[OF disjoint])
  show ?thesis
    using False item_same
    by (simp add: raw_next_at_def raw_prev_at_def)
qed

lemma raw_cycle_observations_survive_index_update:
  assumes layout: "raw_xlist_layout lp rs"
    and member: "u \<in> insert (raw_end_item lp) (set rs)"
  shows
    "raw_next_at
       (heap_update lp
         (pxIndex_C_update (\<lambda>_. q) (h_val h lp)) h) lp u =
       raw_next_at h lp u \<and>
     raw_prev_at
       (heap_update lp
         (pxIndex_C_update (\<lambda>_. q) (h_val h lp)) h) lp u =
       raw_prev_at h lp u"
  apply (rule raw_cycle_observations_survive_list_update[OF layout member])
  by simp

lemma raw_cycle_observations_survive_count_update:
  assumes layout: "raw_xlist_layout lp rs"
    and member: "u \<in> insert (raw_end_item lp) (set rs)"
  shows
    "raw_next_at
       (heap_update lp
         (uxNumberOfItems_C_update f (h_val h lp)) h) lp u =
       raw_next_at h lp u \<and>
     raw_prev_at
       (heap_update lp
         (uxNumberOfItems_C_update f (h_val h lp)) h) lp u =
       raw_prev_at h lp u"
  apply (rule raw_cycle_observations_survive_list_update[OF layout member])
  by simp

lemma raw_remaining_cycle_observations_survive_container_update:
  assumes layout: "raw_xlist_layout lp rs"
    and distinct: "distinct rs"
    and p_member: "p \<in> set rs"
    and u_member:
      "u \<in> insert (raw_end_item lp) (set (remove1 p rs))"
  shows
    "raw_next_at
       (heap_update p
         (pvContainer_C_update f (v :: xLIST_ITEM_C)) h) lp u =
       raw_next_at h lp u \<and>
     raw_prev_at
       (heap_update p (pvContainer_C_update f v) h) lp u =
       raw_prev_at h lp u"
proof (cases "u = raw_end_item lp")
  case True
  have disjoint:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using layout p_member by (auto simp: raw_xlist_layout_def)
  have list_same:
    "h_val (heap_update p (pvContainer_C_update f v) h) lp = h_val h lp"
    by (rule raw_item_update_preserves_disjoint_list[OF disjoint])
  show ?thesis
    using True list_same
    by (simp add: raw_next_at_def raw_prev_at_def)
next
  case False
  have u_remaining: "u \<in> set (remove1 p rs)"
    using u_member False by simp
  have u_original: "u \<in> set rs"
    using set_remove1_subset u_remaining by (meson subsetD)
  have p_not_remaining: "p \<notin> set (remove1 p rs)"
    by (rule raw_distinct_member_notin_remove1[OF distinct p_member])
  have different: "p \<noteq> u"
    using p_not_remaining u_remaining by auto
  have disjoint:
    "raw_item_region p \<inter> raw_item_region u = {}"
    using layout p_member u_original different
    by (auto simp: raw_xlist_layout_def)
  have item_same:
    "h_val (heap_update p (pvContainer_C_update f v) h) u = h_val h u"
    by (rule raw_item_update_preserves_disjoint_item[OF disjoint])
  show ?thesis
    using False item_same
    by (simp add: raw_next_at_def raw_prev_at_def)
qed

lemma raw_ring_links_observation_cong:
  assumes links: "raw_ring_links h lp rs"
    and observations:
      "\<And>u. u \<in> insert (raw_end_item lp) (set rs) \<Longrightarrow>
        raw_next_at h' lp u = raw_next_at h lp u \<and>
        raw_prev_at h' lp u = raw_prev_at h lp u"
  shows "raw_ring_links h' lp rs"
  unfolding raw_ring_links_def list_all_iff
proof (intro ballI)
  fix uv
  assume uv_member: "uv \<in> set (raw_edge_pairs lp rs)"
  obtain u v where uv: "uv = (u, v)"
    by (cases uv) simp
  have uv_pair: "(u, v) \<in> set (raw_edge_pairs lp rs)"
    using uv_member uv by simp
  have u_source: "u \<in> set (map fst (raw_edge_pairs lp rs))"
    unfolding set_map
    apply (rule image_eqI[where x="(u, v)"])
    using uv_pair by simp_all
  have v_target: "v \<in> set (map snd (raw_edge_pairs lp rs))"
    unfolding set_map
    apply (rule image_eqI[where x="(u, v)"])
    using uv_pair by simp_all
  have u_cycle: "u \<in> insert (raw_end_item lp) (set rs)"
    using u_source by simp
  have v_cycle: "v \<in> insert (raw_end_item lp) (set rs)"
    using v_target by simp
  have all_edges:
    "\<forall>x \<in> set (raw_edge_pairs lp rs).
       case x of (a, b) \<Rightarrow>
         raw_next_at h lp a = b \<and> raw_prev_at h lp b = a"
    using links by (simp add: raw_ring_links_def list_all_iff)
  have pair_edge:
    "(case (u, v) of (a, b) \<Rightarrow>
       raw_next_at h lp a = b \<and> raw_prev_at h lp b = a)"
    by (rule all_edges[rule_format, OF uv_pair])
  have old_edge:
    "raw_next_at h lp u = v \<and> raw_prev_at h lp v = u"
    using pair_edge by simp
  have u_observations:
    "raw_next_at h' lp u = raw_next_at h lp u \<and>
     raw_prev_at h' lp u = raw_prev_at h lp u"
    by (rule observations[OF u_cycle])
  have v_observations:
    "raw_next_at h' lp v = raw_next_at h lp v \<and>
     raw_prev_at h' lp v = raw_prev_at h lp v"
    by (rule observations[OF v_cycle])
  show
    "(case uv of (p, q) \<Rightarrow>
       raw_next_at h' lp p = q \<and> raw_prev_at h' lp q = p)"
    using old_edge u_observations v_observations uv by simp
qed

lemma raw_ring_links_survives_index_update:
  assumes layout: "raw_xlist_layout lp rs"
    and links: "raw_ring_links h lp rs"
  shows
    "raw_ring_links
       (heap_update lp
         (pxIndex_C_update (\<lambda>_. q) (h_val h lp)) h) lp rs"
proof (rule raw_ring_links_observation_cong[OF links])
  fix u
  assume member: "u \<in> insert (raw_end_item lp) (set rs)"
  show
    "raw_next_at
       (heap_update lp
         (pxIndex_C_update (\<lambda>_. q) (h_val h lp)) h) lp u =
       raw_next_at h lp u \<and>
     raw_prev_at
       (heap_update lp
         (pxIndex_C_update (\<lambda>_. q) (h_val h lp)) h) lp u =
       raw_prev_at h lp u"
    by (rule raw_cycle_observations_survive_index_update[OF layout member])
qed

lemma raw_ring_links_survives_count_update:
  assumes layout: "raw_xlist_layout lp rs"
    and links: "raw_ring_links h lp rs"
  shows
    "raw_ring_links
       (heap_update lp
         (uxNumberOfItems_C_update f (h_val h lp)) h) lp rs"
proof (rule raw_ring_links_observation_cong[OF links])
  fix u
  assume member: "u \<in> insert (raw_end_item lp) (set rs)"
  show
    "raw_next_at
       (heap_update lp
         (uxNumberOfItems_C_update f (h_val h lp)) h) lp u =
       raw_next_at h lp u \<and>
     raw_prev_at
       (heap_update lp
         (uxNumberOfItems_C_update f (h_val h lp)) h) lp u =
       raw_prev_at h lp u"
    by (rule raw_cycle_observations_survive_count_update[OF layout member])
qed

lemma raw_ring_links_survives_removed_container_update:
  assumes layout: "raw_xlist_layout lp rs"
    and distinct: "distinct rs"
    and member: "p \<in> set rs"
    and links: "raw_ring_links h lp (remove1 p rs)"
  shows
    "raw_ring_links
       (heap_update p
         (pvContainer_C_update f (v :: xLIST_ITEM_C)) h)
       lp (remove1 p rs)"
proof (rule raw_ring_links_observation_cong[OF links])
  fix u
  assume u_member:
    "u \<in> insert (raw_end_item lp) (set (remove1 p rs))"
  show
    "raw_next_at
       (heap_update p (pvContainer_C_update f v) h) lp u =
       raw_next_at h lp u \<and>
     raw_prev_at
       (heap_update p (pvContainer_C_update f v) h) lp u =
       raw_prev_at h lp u"
    by (rule raw_remaining_cycle_observations_survive_container_update[
          OF layout distinct member u_member])
qed

lemma raw_remove_taken_suffix_preserves_ring_links:
  assumes layout: "raw_xlist_layout lp rs"
    and distinct: "distinct rs"
    and member: "p \<in> set rs"
    and links: "raw_ring_links h lp (remove1 p rs)"
  shows
    "raw_ring_links (raw_remove_taken_suffix_heap h lp p) lp
       (remove1 p rs)"
proof -
  let ?remaining = "remove1 p rs"
  let ?hi = "raw_remove_taken_index_heap h lp p"
  let ?hc = "raw_remove_container_heap ?hi p"
  have remaining_layout: "raw_xlist_layout lp ?remaining"
    by (rule raw_xlist_layout_remove1[OF layout])
  have index_links: "raw_ring_links ?hi lp ?remaining"
    unfolding raw_remove_taken_index_heap_def
    by (rule raw_ring_links_survives_index_update[
          OF remaining_layout links])
  have container_links: "raw_ring_links ?hc lp ?remaining"
    unfolding raw_remove_container_heap_def
    by (rule raw_ring_links_survives_removed_container_update[
          OF layout distinct member index_links])
  have count_links:
    "raw_ring_links (raw_remove_count_heap ?hc lp) lp ?remaining"
    unfolding raw_remove_count_heap_def
    by (rule raw_ring_links_survives_count_update[
          OF remaining_layout container_links])
  show ?thesis
    using count_links by (simp add: raw_remove_taken_suffix_heap_def)
qed

lemma raw_remove_plain_suffix_preserves_ring_links:
  assumes layout: "raw_xlist_layout lp rs"
    and distinct: "distinct rs"
    and member: "p \<in> set rs"
    and links: "raw_ring_links h lp (remove1 p rs)"
  shows
    "raw_ring_links (raw_remove_plain_suffix_heap h lp p) lp
       (remove1 p rs)"
proof -
  let ?remaining = "remove1 p rs"
  let ?hc = "raw_remove_container_heap h p"
  have remaining_layout: "raw_xlist_layout lp ?remaining"
    by (rule raw_xlist_layout_remove1[OF layout])
  have container_links: "raw_ring_links ?hc lp ?remaining"
    unfolding raw_remove_container_heap_def
    by (rule raw_ring_links_survives_removed_container_update[
          OF layout distinct member links])
  have count_links:
    "raw_ring_links (raw_remove_count_heap ?hc lp) lp ?remaining"
    unfolding raw_remove_count_heap_def
    by (rule raw_ring_links_survives_count_update[
          OF remaining_layout container_links])
  show ?thesis
    using count_links by (simp add: raw_remove_plain_suffix_heap_def)
qed

lemma raw_source_unlink_two_ring_links:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_ring_links (raw_source_unlink_two h p) lp
       (remove1 p (ring xs))"
  using raw_source_unlink_two_eq[OF rel member]
    raw_unlink_two_writes_ring_links[OF rel member]
  by simp

lemma raw_remove_taken_source_topology_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_ring_links
       (raw_remove_taken_suffix_heap (raw_source_unlink_two h p) lp p)
       lp (remove1 p (ring xs))"
proof -
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have distinct: "distinct (ring xs)"
    using raw_xlist_rel_distinct_cycle_nodes[OF rel] by simp
  have links:
    "raw_ring_links (raw_source_unlink_two h p) lp
       (remove1 p (ring xs))"
    by (rule raw_source_unlink_two_ring_links[OF rel member])
  show ?thesis
    by (rule raw_remove_taken_suffix_preserves_ring_links[
          OF layout distinct member links])
qed

lemma raw_remove_plain_source_topology_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_ring_links
       (raw_remove_plain_suffix_heap (raw_source_unlink_two h p) lp p)
       lp (remove1 p (ring xs))"
proof -
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have distinct: "distinct (ring xs)"
    using raw_xlist_rel_distinct_cycle_nodes[OF rel] by simp
  have links:
    "raw_ring_links (raw_source_unlink_two h p) lp
       (remove1 p (ring xs))"
    by (rule raw_source_unlink_two_ring_links[OF rel member])
  show ?thesis
    by (rule raw_remove_plain_suffix_preserves_ring_links[
          OF layout distinct member links])
qed

lemma raw_remove_concrete_heap_topology_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_ring_links (raw_remove_concrete_heap h p) lp
       (remove1 p (ring xs))"
proof (cases
    "pxIndex_C (h_val (raw_source_unlink_two h p) lp) = p")
  case True
  have cast:
    "PTR_COERCE(unit \<rightarrow> xLIST_C)
       (pvContainer_C (h_val (raw_source_unlink_two h p) p)) = lp"
    by (rule raw_source_unlink_two_container_cast[OF rel member])
  have heap_eq:
    "raw_remove_concrete_heap h p =
       raw_remove_taken_suffix_heap (raw_source_unlink_two h p) lp p"
    using True cast
    by (simp add: raw_remove_concrete_heap_def raw_remove_suffix_heap_def
        raw_remove_index_heap_def raw_remove_taken_index_heap_def
        raw_remove_taken_suffix_heap_def Let_def)
  show ?thesis
    using raw_remove_taken_source_topology_effect[OF rel member] heap_eq
    by simp
next
  case False
  have cast:
    "PTR_COERCE(unit \<rightarrow> xLIST_C)
       (pvContainer_C (h_val (raw_source_unlink_two h p) p)) = lp"
    by (rule raw_source_unlink_two_container_cast[OF rel member])
  have heap_eq:
    "raw_remove_concrete_heap h p =
       raw_remove_plain_suffix_heap (raw_source_unlink_two h p) lp p"
    using False cast
    by (simp add: raw_remove_concrete_heap_def raw_remove_suffix_heap_def
        raw_remove_index_heap_def raw_remove_plain_suffix_heap_def Let_def)
  show ?thesis
    using raw_remove_plain_source_topology_effect[OF rel member] heap_eq
    by simp
qed

theorem raw_vListRemove_general_topology_effect:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       raw_ring_links (hrs_mem (t_hrs_' t)) lp
         (remove1 p (ring xs))
     \<rbrace>"
proof -
  note heap_effect = raw_vListRemove_general_heap_effect[OF rel member]
  note topology_effect = raw_remove_concrete_heap_topology_effect[OF rel member]
  show ?thesis
    apply (rule runs_to_weaken[OF heap_effect])
    using topology_effect
    by auto
qed

end
