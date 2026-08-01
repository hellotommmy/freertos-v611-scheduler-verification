theory Scheduler_P2_Remove_Cross_List
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Wake_Key.Scheduler_P2_Wake_Key"
begin

text \<open>
  A singleton removal touches its source root, the removed item, and the two
  link fields in the source sentinel.  The footprint separates all of those
  byte regions from a different scheduler root.  This leaf packages that
  cross-list locality without opening either generated C body.
\<close>

lemma raw_remove_singleton_link_fields:
  assumes rel: "raw_xlist_rel h lp xs"
    and singleton: "ring xs = [p]"
  shows
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxPrevious_C
       (h_val h p) = raw_end_item lp \<and>
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxNext_C
       (h_val h p) = raw_end_item lp"
proof -
  have layout: "raw_xlist_layout lp [p]"
    using rel singleton by (simp add: raw_xlist_rel_def)
  have not_end: "p \<noteq> raw_end_item lp"
    using layout by (auto simp: raw_xlist_layout_def)
  have links: "raw_ring_links h lp [p]"
    using rel singleton
    by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  show ?thesis
    using iffD1[OF raw_ring_links_singleton_iff[OF not_end] links]
    by blast
qed

lemma raw_source_unlink_two_singleton_preserves_disjoint_list:
  assumes rel: "raw_xlist_rel h lp xs"
    and singleton: "ring xs = [p]"
    and roots:
      "raw_list_region lp \<inter> raw_list_region lq = {}"
  shows
    "h_val (raw_source_unlink_two h p) lq = h_val h lq"
proof -
  have member: "p \<in> set (ring xs)"
    using singleton by simp
  note fields = raw_remove_singleton_link_fields[OF rel singleton]
  let ?h1 = "raw_source_unlink_first h p"
  have first_subset:
    "raw_pointer_field_region
       (raw_previous_field_ptr
         (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxNext_C
           (h_val h p))) \<subseteq>
     raw_list_region lp"
    using fields
      raw_end_previous_field_region_subset_list[where lp=lp]
    by simp
  have first_disjoint:
    "raw_pointer_field_region
       (raw_previous_field_ptr
         (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxNext_C
           (h_val h p))) \<inter>
     raw_list_region lq = {}"
    using first_subset roots by blast
  have h1_target: "h_val ?h1 lq = h_val h lq"
    unfolding raw_source_unlink_first_def
    by (rule raw_pointer_field_update_preserves_disjoint_list[
          OF first_disjoint])
  have h1_item: "h_val ?h1 p = h_val h p"
    unfolding raw_source_unlink_first_def
    by (rule raw_remove_first_unlink_preserves_item[OF rel member])
  have second_subset:
    "raw_pointer_field_region
       (raw_next_field_ptr
         (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxPrevious_C
           (h_val ?h1 p))) \<subseteq>
     raw_list_region lp"
    using fields h1_item
      raw_end_next_field_region_subset_list[where lp=lp]
    by simp
  have second_disjoint:
    "raw_pointer_field_region
       (raw_next_field_ptr
         (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxPrevious_C
           (h_val ?h1 p))) \<inter>
     raw_list_region lq = {}"
    using second_subset roots by blast
  have h2_target:
    "h_val (raw_source_unlink_two h p) lq = h_val ?h1 lq"
    unfolding raw_source_unlink_two_def
    by (rule raw_pointer_field_update_preserves_disjoint_list[
          OF second_disjoint])
  show ?thesis using h2_target h1_target by simp
qed

lemma raw_remove_suffix_preserves_disjoint_list:
  assumes roots:
      "raw_list_region lp \<inter> raw_list_region lq = {}"
    and item_target:
      "raw_item_region p \<inter> raw_list_region lq = {}"
  shows
    "h_val (raw_remove_suffix_heap h lp p) lq = h_val h lq"
proof -
  let ?hi = "raw_remove_index_heap h lp p"
  let ?hc = "raw_remove_container_heap ?hi p"
  have index_target: "h_val ?hi lq = h_val h lq"
  proof (cases
      "List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C
         (h_val h lp) = p")
    case True
    show ?thesis
      unfolding raw_remove_index_heap_def
      apply (simp only: if_P[OF True])
      by (rule raw_list_update_preserves_disjoint_list[OF roots])
  next
    case False
    show ?thesis
      unfolding raw_remove_index_heap_def
      by (simp only: if_not_P[OF False])
  qed
  have container_target: "h_val ?hc lq = h_val ?hi lq"
    unfolding raw_remove_container_heap_def
    by (rule raw_item_update_preserves_disjoint_list[OF item_target])
  have count_target:
    "h_val (raw_remove_count_heap ?hc lp) lq = h_val ?hc lq"
    unfolding raw_remove_count_heap_def
    by (rule raw_list_update_preserves_disjoint_list[OF roots])
  have
    "h_val (raw_remove_suffix_heap h lp p) lq =
     h_val (raw_remove_count_heap ?hc lp) lq"
    by (simp only: raw_remove_suffix_heap_def)
  also have "... = h_val ?hc lq" by (rule count_target)
  also have "... = h_val ?hi lq" by (rule container_target)
  also have "... = h_val h lq" by (rule index_target)
  finally show ?thesis .
qed

lemma raw_remove_singleton_preserves_disjoint_list:
  assumes rel: "raw_xlist_rel h lp xs"
    and singleton: "ring xs = [p]"
    and roots:
      "raw_list_region lp \<inter> raw_list_region lq = {}"
    and item_target:
      "raw_item_region p \<inter> raw_list_region lq = {}"
  shows
    "h_val (raw_remove_concrete_heap h p) lq = h_val h lq"
proof -
  have member: "p \<in> set (ring xs)"
    using singleton by simp
  have concrete:
    "raw_remove_concrete_heap h p = raw_remove_source_heap h lp p"
    by (rule raw_remove_concrete_heap_eq[OF rel member])
  have unlink:
    "h_val (raw_source_unlink_two h p) lq = h_val h lq"
    by (rule raw_source_unlink_two_singleton_preserves_disjoint_list[
          OF rel singleton roots])
  have suffix:
    "h_val
       (raw_remove_suffix_heap (raw_source_unlink_two h p) lp p) lq =
     h_val (raw_source_unlink_two h p) lq"
    by (rule raw_remove_suffix_preserves_disjoint_list[
          OF roots item_target])
  show ?thesis
    using concrete suffix unlink
    by (simp only: raw_remove_source_heap_def)
qed

end
