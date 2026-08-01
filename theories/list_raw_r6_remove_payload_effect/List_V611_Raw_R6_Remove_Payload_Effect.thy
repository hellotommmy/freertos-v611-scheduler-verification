theory List_V611_Raw_R6_Remove_Payload_Effect
  imports "EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Source_Effects.List_V611_Raw_R6_Remove_Source_Effects"
begin

text \<open>
  General-N removal payload frame.  The two unlink writes may target a
  surviving predecessor or successor, so locality is proved at the key and
  container projections rather than by claiming that each surviving item is
  byte-for-byte unchanged.  The later list-metadata writes and the removed
  item's container write are then discharged by allocation-region
  disjointness.
\<close>

lemma raw_distinct_remove1_survivorD:
  assumes distinct: "distinct rs"
    and member: "p \<in> set rs"
    and survivor: "q \<in> set (remove1 p rs)"
  shows "q \<in> set rs \<and> q \<noteq> p"
proof -
  have q_member: "q \<in> set rs"
    by (rule subsetD[OF set_remove1_subset survivor])
  have p_not: "p \<notin> set (remove1 p rs)"
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
  show ?thesis using q_member p_not survivor by auto
qed

lemma raw_list_update_preserves_disjoint_item:
  assumes disjoint:
    "raw_list_region lp \<inter> raw_item_region q = {}"
  shows
    "h_val (heap_update lp (v :: xLIST_C) h) q = h_val h q"
proof -
  have byte_disjoint:
    "{ptr_val lp..+
       length (to_bytes v
         (heap_list h (size_of TYPE(xLIST_C)) (ptr_val lp)))} \<inter>
     {ptr_val q..+size_of TYPE(xLIST_ITEM_C)} = {}"
    using disjoint
    by (simp add: raw_list_region_def raw_item_region_def)
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

lemma raw_layout_list_update_preserves_live_item:
  assumes layout: "raw_xlist_layout lp rs"
    and member: "q \<in> set rs"
  shows
    "h_val (heap_update lp (v :: xLIST_C) h) q = h_val h q"
proof -
  have item_list:
    "raw_item_region q \<inter> raw_list_region lp = {}"
    using layout member by (auto simp: raw_xlist_layout_def)
  have list_item:
    "raw_list_region lp \<inter> raw_item_region q = {}"
    using item_list by blast
  show ?thesis
    by (rule raw_list_update_preserves_disjoint_item[OF list_item])
qed

lemma raw_cycle_next_field_update_preserves_payload:
  assumes layout: "raw_xlist_layout lp rs"
    and write_member:
      "u \<in> insert (raw_end_item lp) (set rs)"
    and live_member: "q \<in> set rs"
  shows
    "raw_key_at (heap_update (raw_next_field_ptr u) v h) q =
       raw_key_at h q \<and>
     pvContainer_C
       (h_val (heap_update (raw_next_field_ptr u) v h) q) =
       pvContainer_C (h_val h q)"
proof (cases "u = q")
  case True
  have guard: "c_guard u"
    using layout write_member
    by (auto simp: raw_xlist_layout_def)
  show ?thesis
    using raw_next_field_update_to_whole[
        OF guard, where q=v and h=h]
      guard True
    by (simp add: raw_key_at_def h_val_heap_update)
next
  case False
  have field_disjoint:
    "raw_pointer_field_region (raw_next_field_ptr u) \<inter>
     raw_item_region q = {}"
    by (rule raw_cycle_next_field_disjoint_from_other_item[
          OF layout live_member write_member False])
  have item_same:
    "h_val (heap_update (raw_next_field_ptr u) v h) q = h_val h q"
    by (rule raw_pointer_field_update_preserves_disjoint_item[
          OF field_disjoint])
  show ?thesis using item_same by (simp add: raw_key_at_def)
qed

lemma raw_cycle_previous_field_update_preserves_payload:
  assumes layout: "raw_xlist_layout lp rs"
    and write_member:
      "u \<in> insert (raw_end_item lp) (set rs)"
    and live_member: "q \<in> set rs"
  shows
    "raw_key_at (heap_update (raw_previous_field_ptr u) v h) q =
       raw_key_at h q \<and>
     pvContainer_C
       (h_val (heap_update (raw_previous_field_ptr u) v h) q) =
       pvContainer_C (h_val h q)"
proof (cases "u = q")
  case True
  have guard: "c_guard u"
    using layout write_member
    by (auto simp: raw_xlist_layout_def)
  show ?thesis
    using raw_previous_field_update_to_whole[
        OF guard, where q=v and h=h]
      guard True
    by (simp add: raw_key_at_def h_val_heap_update)
next
  case False
  have field_disjoint:
    "raw_pointer_field_region (raw_previous_field_ptr u) \<inter>
     raw_item_region q = {}"
    by (rule raw_cycle_previous_field_disjoint_from_other_item[
          OF layout live_member write_member False])
  have item_same:
    "h_val (heap_update (raw_previous_field_ptr u) v h) q = h_val h q"
    by (rule raw_pointer_field_update_preserves_disjoint_item[
          OF field_disjoint])
  show ?thesis using item_same by (simp add: raw_key_at_def)
qed

lemma raw_unlink_two_preserves_live_payload:
  assumes rel: "raw_xlist_rel h lp xs"
    and removed: "p \<in> set (ring xs)"
    and live: "q \<in> set (ring xs)"
  shows
    "raw_key_at (raw_unlink_two h lp p) q = raw_key_at h q \<and>
     pvContainer_C (h_val (raw_unlink_two h lp p) q) =
       pvContainer_C (h_val h q)"
proof -
  let ?cycle = "insert (raw_end_item lp) (set (ring xs))"
  let ?a = "raw_prev_at h lp p"
  let ?b = "raw_next_at h lp p"
  let ?h1 = "raw_unlink_first h lp p"
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have p_cycle: "p \<in> ?cycle" using removed by simp
  have a_cycle: "?a \<in> ?cycle"
    by (rule raw_ring_links_prev_closed[OF links p_cycle])
  have b_cycle: "?b \<in> ?cycle"
    by (rule raw_ring_links_next_closed[OF links p_cycle])
  have first:
    "raw_key_at ?h1 q = raw_key_at h q \<and>
     pvContainer_C (h_val ?h1 q) = pvContainer_C (h_val h q)"
    unfolding raw_unlink_first_def
    by (rule raw_cycle_previous_field_update_preserves_payload[
          OF layout b_cycle live])
  have second:
    "raw_key_at (raw_unlink_two h lp p) q = raw_key_at ?h1 q \<and>
     pvContainer_C (h_val (raw_unlink_two h lp p) q) =
       pvContainer_C (h_val ?h1 q)"
    unfolding raw_unlink_two_def
    by (rule raw_cycle_next_field_update_preserves_payload[
          OF layout a_cycle live])
  show ?thesis using first second by auto
qed

lemma raw_source_unlink_two_preserves_live_payload:
  assumes rel: "raw_xlist_rel h lp xs"
    and removed: "p \<in> set (ring xs)"
    and live: "q \<in> set (ring xs)"
  shows
    "raw_key_at (raw_source_unlink_two h p) q = raw_key_at h q \<and>
     pvContainer_C (h_val (raw_source_unlink_two h p) q) =
       pvContainer_C (h_val h q)"
  using raw_source_unlink_two_eq[OF rel removed]
    raw_unlink_two_preserves_live_payload[OF rel removed live]
  by simp

lemma raw_remove_taken_index_heap_preserves_live_item:
  assumes layout: "raw_xlist_layout lp rs"
    and live: "q \<in> set rs"
  shows
    "h_val (raw_remove_taken_index_heap h lp p) q = h_val h q"
  unfolding raw_remove_taken_index_heap_def
  by (rule raw_layout_list_update_preserves_live_item[OF layout live])

lemma raw_remove_container_heap_preserves_other_item:
  assumes layout: "raw_xlist_layout lp rs"
    and removed: "p \<in> set rs"
    and live: "q \<in> set rs"
    and different: "q \<noteq> p"
  shows
    "h_val (raw_remove_container_heap h p) q = h_val h q"
proof -
  have disjoint:
    "raw_item_region p \<inter> raw_item_region q = {}"
    using layout removed live different
    by (auto simp: raw_xlist_layout_def)
  show ?thesis
    unfolding raw_remove_container_heap_def
    by (rule raw_item_update_preserves_disjoint_item[OF disjoint])
qed

lemma raw_remove_count_heap_preserves_live_item:
  assumes layout: "raw_xlist_layout lp rs"
    and live: "q \<in> set rs"
  shows
    "h_val (raw_remove_count_heap h lp) q = h_val h q"
  unfolding raw_remove_count_heap_def
  by (rule raw_layout_list_update_preserves_live_item[OF layout live])

lemma raw_remove_taken_suffix_heap_preserves_other_item:
  assumes layout: "raw_xlist_layout lp rs"
    and removed: "p \<in> set rs"
    and live: "q \<in> set rs"
    and different: "q \<noteq> p"
  shows
    "h_val (raw_remove_taken_suffix_heap h lp p) q = h_val h q"
proof -
  let ?hi = "raw_remove_taken_index_heap h lp p"
  let ?hc = "raw_remove_container_heap ?hi p"
  have index_same: "h_val ?hi q = h_val h q"
    by (rule raw_remove_taken_index_heap_preserves_live_item[
          OF layout live])
  have container_same: "h_val ?hc q = h_val ?hi q"
    by (rule raw_remove_container_heap_preserves_other_item[
          OF layout removed live different])
  have count_same:
    "h_val (raw_remove_count_heap ?hc lp) q = h_val ?hc q"
    by (rule raw_remove_count_heap_preserves_live_item[OF layout live])
  show ?thesis
    using index_same container_same count_same
    by (simp add: raw_remove_taken_suffix_heap_def)
qed

lemma raw_remove_plain_suffix_heap_preserves_other_item:
  assumes layout: "raw_xlist_layout lp rs"
    and removed: "p \<in> set rs"
    and live: "q \<in> set rs"
    and different: "q \<noteq> p"
  shows
    "h_val (raw_remove_plain_suffix_heap h lp p) q = h_val h q"
proof -
  let ?hc = "raw_remove_container_heap h p"
  have container_same: "h_val ?hc q = h_val h q"
    by (rule raw_remove_container_heap_preserves_other_item[
          OF layout removed live different])
  have count_same:
    "h_val (raw_remove_count_heap ?hc lp) q = h_val ?hc q"
    by (rule raw_remove_count_heap_preserves_live_item[OF layout live])
  show ?thesis
    using container_same count_same
    by (simp add: raw_remove_plain_suffix_heap_def)
qed

lemma raw_remove_taken_source_payload_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and removed: "p \<in> set (ring xs)"
  shows
    "\<forall>q \<in> set (remove1 p (ring xs)).
       raw_key_at
         (raw_remove_taken_suffix_heap
           (raw_source_unlink_two h p) lp p) q =
         raw_key_at h q \<and>
       pvContainer_C
         (h_val
           (raw_remove_taken_suffix_heap
             (raw_source_unlink_two h p) lp p) q) =
         pvContainer_C (h_val h q)"
proof (intro ballI)
  fix q
  assume survivor: "q \<in> set (remove1 p (ring xs))"
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have distinct: "distinct (ring xs)"
    using raw_xlist_rel_distinct_cycle_nodes[OF rel] by simp
  have survivor_info:
    "q \<in> set (ring xs) \<and> q \<noteq> p"
    by (rule raw_distinct_remove1_survivorD[
          OF distinct removed survivor])
  have live: "q \<in> set (ring xs)"
    using survivor_info by simp
  have different: "q \<noteq> p"
    using survivor_info by simp
  have unlink:
    "raw_key_at (raw_source_unlink_two h p) q = raw_key_at h q \<and>
     pvContainer_C (h_val (raw_source_unlink_two h p) q) =
       pvContainer_C (h_val h q)"
    by (rule raw_source_unlink_two_preserves_live_payload[
          OF rel removed live])
  have suffix:
    "h_val
       (raw_remove_taken_suffix_heap
         (raw_source_unlink_two h p) lp p) q =
     h_val (raw_source_unlink_two h p) q"
    by (rule raw_remove_taken_suffix_heap_preserves_other_item[
          OF layout removed live different])
  show
    "raw_key_at
       (raw_remove_taken_suffix_heap
         (raw_source_unlink_two h p) lp p) q = raw_key_at h q \<and>
     pvContainer_C
       (h_val
         (raw_remove_taken_suffix_heap
           (raw_source_unlink_two h p) lp p) q) =
       pvContainer_C (h_val h q)"
    using unlink suffix by (simp add: raw_key_at_def)
qed

lemma raw_remove_plain_source_payload_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and removed: "p \<in> set (ring xs)"
  shows
    "\<forall>q \<in> set (remove1 p (ring xs)).
       raw_key_at
         (raw_remove_plain_suffix_heap
           (raw_source_unlink_two h p) lp p) q =
         raw_key_at h q \<and>
       pvContainer_C
         (h_val
           (raw_remove_plain_suffix_heap
             (raw_source_unlink_two h p) lp p) q) =
         pvContainer_C (h_val h q)"
proof (intro ballI)
  fix q
  assume survivor: "q \<in> set (remove1 p (ring xs))"
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have distinct: "distinct (ring xs)"
    using raw_xlist_rel_distinct_cycle_nodes[OF rel] by simp
  have survivor_info:
    "q \<in> set (ring xs) \<and> q \<noteq> p"
    by (rule raw_distinct_remove1_survivorD[
          OF distinct removed survivor])
  have live: "q \<in> set (ring xs)"
    using survivor_info by simp
  have different: "q \<noteq> p"
    using survivor_info by simp
  have unlink:
    "raw_key_at (raw_source_unlink_two h p) q = raw_key_at h q \<and>
     pvContainer_C (h_val (raw_source_unlink_two h p) q) =
       pvContainer_C (h_val h q)"
    by (rule raw_source_unlink_two_preserves_live_payload[
          OF rel removed live])
  have suffix:
    "h_val
       (raw_remove_plain_suffix_heap
         (raw_source_unlink_two h p) lp p) q =
     h_val (raw_source_unlink_two h p) q"
    by (rule raw_remove_plain_suffix_heap_preserves_other_item[
          OF layout removed live different])
  show
    "raw_key_at
       (raw_remove_plain_suffix_heap
         (raw_source_unlink_two h p) lp p) q = raw_key_at h q \<and>
     pvContainer_C
       (h_val
         (raw_remove_plain_suffix_heap
           (raw_source_unlink_two h p) lp p) q) =
       pvContainer_C (h_val h q)"
    using unlink suffix by (simp add: raw_key_at_def)
qed

lemma raw_remove_concrete_heap_payload_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "\<forall>q \<in> set (remove1 p (ring xs)).
       raw_key_at (raw_remove_concrete_heap h p) q = raw_key_at h q \<and>
       pvContainer_C (h_val (raw_remove_concrete_heap h p) q) =
         pvContainer_C (h_val h q)"
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
    using raw_remove_taken_source_payload_effect[OF rel member] heap_eq
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
    using raw_remove_plain_source_payload_effect[OF rel member] heap_eq
    by simp
qed

theorem raw_vListRemove_general_payload_effect:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       (\<forall>q \<in> set (remove1 p (ring xs)).
          raw_key_at (hrs_mem (t_hrs_' t)) q =
            raw_key_at (hrs_mem (t_hrs_' s)) q \<and>
          pvContainer_C (h_val (hrs_mem (t_hrs_' t)) q) =
            pvContainer_C (h_val (hrs_mem (t_hrs_' s)) q))
     \<rbrace>"
proof -
  note heap_effect = raw_vListRemove_general_heap_effect[OF rel member]
  note payload_effect = raw_remove_concrete_heap_payload_effect[OF rel member]
  show ?thesis
    apply (rule runs_to_weaken[OF heap_effect])
    using payload_effect
    by auto
qed

end
