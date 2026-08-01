theory List_V611_Raw_R6_Remove_Index_Effect
  imports "EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Source_Effects.List_V611_Raw_R6_Remove_Source_Effects"
begin

text \<open>
  General-N source cursor repair for vListRemove'.  The byte-local prefix
  proves that the two unlink writes cannot change the list's pxIndex field,
  including when either write targets the embedded sentinel.  The source VCG
  then follows its taken and non-taken index branches separately.  The final
  cursor theorem is obtained by weakening the exact source-index theorem and
  the already checked pure cursor transfer lemma.
\<close>

definition raw_index_field_ptr ::
  "xLIST_C ptr \<Rightarrow> raw_node_id ptr"
where
  "raw_index_field_ptr lp =
     PTR(xLIST_ITEM_C ptr) &(lp\<rightarrow>[''pxIndex_C''])"

definition raw_index_field_region :: "xLIST_C ptr \<Rightarrow> addr set"
where
  "raw_index_field_region lp =
     {ptr_val (raw_index_field_ptr lp)..+size_of TYPE(raw_node_id)}"

lemma raw_index_field_region_subset_list:
  "raw_index_field_region lp \<subseteq> raw_list_region lp"
  unfolding raw_index_field_region_def raw_index_field_ptr_def
    raw_list_region_def
  apply (auto simp: field_lvalue_def xLIST_C_pxIndex_C_fl
      size_of_def intvl_def)
  subgoal for k
    apply (rule exI[where x="4 + k"])
    by simp
  done

lemma raw_end_next_field_disjoint_index:
  "raw_pointer_field_region
      (raw_next_field_ptr (raw_end_item lp)) \<inter>
   raw_index_field_region lp = {}"
proof -
  have offsets:
    "{(12 :: addr)..+4} \<inter> {(4 :: addr)..+4} = {}"
  proof -
    have "{(4 :: addr)..+4} \<inter> {(12 :: addr)..+4} = {}"
      apply (rule intvl_disj_left)
      apply simp
      by (simp add: addr_card_def card_word)
    then show ?thesis by (simp add: Int_commute)
  qed
  have shifted:
    "{ptr_val lp + (12 :: addr)..+4} \<inter>
     {ptr_val lp + (4 :: addr)..+4} = {}"
    apply (subst intvl_disj_offset)
    by (rule offsets)
  show ?thesis
    using shifted
    by (simp add: raw_pointer_field_region_def raw_next_field_ptr_def
        raw_index_field_region_def raw_index_field_ptr_def raw_end_item_def
        raw_sentinel_ptr_def field_lvalue_def xLIST_ITEM_C_pxNext_C_fl
        xLIST_C_xListEnd_C_fl xLIST_C_pxIndex_C_fl size_of_def
        add.commute)
qed

lemma raw_end_previous_field_disjoint_index:
  "raw_pointer_field_region
      (raw_previous_field_ptr (raw_end_item lp)) \<inter>
   raw_index_field_region lp = {}"
proof -
  have offsets:
    "{(16 :: addr)..+4} \<inter> {(4 :: addr)..+4} = {}"
  proof -
    have "{(4 :: addr)..+4} \<inter> {(16 :: addr)..+4} = {}"
      apply (rule intvl_disj_left)
      apply simp
      by (simp add: addr_card_def card_word)
    then show ?thesis by (simp add: Int_commute)
  qed
  have shifted:
    "{ptr_val lp + (16 :: addr)..+4} \<inter>
     {ptr_val lp + (4 :: addr)..+4} = {}"
    apply (subst intvl_disj_offset)
    by (rule offsets)
  show ?thesis
    using shifted
    by (simp add: raw_pointer_field_region_def raw_previous_field_ptr_def
        raw_index_field_region_def raw_index_field_ptr_def raw_end_item_def
        raw_sentinel_ptr_def field_lvalue_def
        xLIST_ITEM_C_pxPrevious_C_fl xLIST_C_xListEnd_C_fl
        xLIST_C_pxIndex_C_fl size_of_def add.commute)
qed

lemma raw_cycle_next_field_disjoint_index:
  assumes layout: "raw_xlist_layout lp rs"
    and member: "u \<in> insert (raw_end_item lp) (set rs)"
  shows
    "raw_pointer_field_region (raw_next_field_ptr u) \<inter>
     raw_index_field_region lp = {}"
proof (cases "u = raw_end_item lp")
  case True
  show ?thesis using True raw_end_next_field_disjoint_index by simp
next
  case False
  have u_real: "u \<in> set rs" using member False by simp
  have item_list:
    "raw_item_region u \<inter> raw_list_region lp = {}"
    using layout u_real by (auto simp: raw_xlist_layout_def)
  show ?thesis
    using raw_next_field_region_subset_item[where u=u]
      raw_index_field_region_subset_list[where lp=lp] item_list
    by blast
qed

lemma raw_cycle_previous_field_disjoint_index:
  assumes layout: "raw_xlist_layout lp rs"
    and member: "u \<in> insert (raw_end_item lp) (set rs)"
  shows
    "raw_pointer_field_region (raw_previous_field_ptr u) \<inter>
     raw_index_field_region lp = {}"
proof (cases "u = raw_end_item lp")
  case True
  show ?thesis using True raw_end_previous_field_disjoint_index by simp
next
  case False
  have u_real: "u \<in> set rs" using member False by simp
  have item_list:
    "raw_item_region u \<inter> raw_list_region lp = {}"
    using layout u_real by (auto simp: raw_xlist_layout_def)
  show ?thesis
    using raw_previous_field_region_subset_item[where u=u]
      raw_index_field_region_subset_list[where lp=lp] item_list
    by blast
qed

lemma raw_pointer_update_preserves_disjoint_index_field:
  assumes disjoint:
    "raw_pointer_field_region f \<inter> raw_index_field_region lp = {}"
  shows
    "h_val (heap_update f (q :: raw_node_id) h)
       (raw_index_field_ptr lp) =
     h_val h (raw_index_field_ptr lp)"
proof -
  have byte_disjoint:
    "{ptr_val f..+
       length (to_bytes q
         (heap_list h (size_of TYPE(raw_node_id)) (ptr_val f)))} \<inter>
     {ptr_val (raw_index_field_ptr lp)..+size_of TYPE(raw_node_id)} = {}"
    using disjoint
    by (simp add: raw_pointer_field_region_def raw_index_field_region_def)
  have heap_lists_same:
    "heap_list
       (heap_update_list (ptr_val f)
         (to_bytes q
           (heap_list h (size_of TYPE(raw_node_id)) (ptr_val f))) h)
       (size_of TYPE(raw_node_id)) (ptr_val (raw_index_field_ptr lp)) =
     heap_list h (size_of TYPE(raw_node_id))
       (ptr_val (raw_index_field_ptr lp))"
    by (rule heap_list_update_disjoint_same[OF byte_disjoint])
  show ?thesis
    unfolding h_val_def heap_update_def
    using heap_lists_same by simp
qed

lemma raw_index_field_value:
  "h_val h (raw_index_field_ptr lp) = pxIndex_C (h_val h lp)"
  unfolding raw_index_field_ptr_def
  by (rule xLIST_C_h_val_fields(2))

lemma raw_next_field_update_preserves_index:
  assumes layout: "raw_xlist_layout lp rs"
    and member: "u \<in> insert (raw_end_item lp) (set rs)"
  shows
    "pxIndex_C (h_val (heap_update (raw_next_field_ptr u) q h) lp) =
     pxIndex_C (h_val h lp)"
proof -
  have field_same:
    "h_val (heap_update (raw_next_field_ptr u) q h)
       (raw_index_field_ptr lp) =
     h_val h (raw_index_field_ptr lp)"
    by (rule raw_pointer_update_preserves_disjoint_index_field[
          OF raw_cycle_next_field_disjoint_index[OF layout member]])
  show ?thesis
    using raw_index_field_value[
        where h="heap_update (raw_next_field_ptr u) q h" and lp=lp]
      raw_index_field_value[where h=h and lp=lp] field_same
    by simp
qed

lemma raw_previous_field_update_preserves_index:
  assumes layout: "raw_xlist_layout lp rs"
    and member: "u \<in> insert (raw_end_item lp) (set rs)"
  shows
    "pxIndex_C
       (h_val (heap_update (raw_previous_field_ptr u) q h) lp) =
     pxIndex_C (h_val h lp)"
proof -
  have field_same:
    "h_val (heap_update (raw_previous_field_ptr u) q h)
       (raw_index_field_ptr lp) =
     h_val h (raw_index_field_ptr lp)"
    by (rule raw_pointer_update_preserves_disjoint_index_field[
          OF raw_cycle_previous_field_disjoint_index[OF layout member]])
  show ?thesis
    using raw_index_field_value[
        where h="heap_update (raw_previous_field_ptr u) q h" and lp=lp]
      raw_index_field_value[where h=h and lp=lp] field_same
    by simp
qed

lemma raw_unlink_two_preserves_index:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "pxIndex_C (h_val (raw_unlink_two h lp p) lp) =
     pxIndex_C (h_val h lp)"
proof -
  let ?cycle = "insert (raw_end_item lp) (set (ring xs))"
  let ?a = "raw_prev_at h lp p"
  let ?b = "raw_next_at h lp p"
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have p_cycle: "p \<in> ?cycle" using member by simp
  have a_cycle: "?a \<in> ?cycle"
    by (rule raw_ring_links_prev_closed[OF links p_cycle])
  have b_cycle: "?b \<in> ?cycle"
    by (rule raw_ring_links_next_closed[OF links p_cycle])
  have first:
    "pxIndex_C (h_val (raw_unlink_first h lp p) lp) =
     pxIndex_C (h_val h lp)"
    unfolding raw_unlink_first_def
    by (rule raw_previous_field_update_preserves_index[
          OF layout b_cycle])
  have second:
    "pxIndex_C (h_val (raw_unlink_two h lp p) lp) =
     pxIndex_C (h_val (raw_unlink_first h lp p) lp)"
    unfolding raw_unlink_two_def
    by (rule raw_next_field_update_preserves_index[OF layout a_cycle])
  show ?thesis using first second by simp
qed

lemma raw_source_unlink_two_preserves_index:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "pxIndex_C (h_val (raw_source_unlink_two h p) lp) =
     pxIndex_C (h_val h lp)"
  using raw_source_unlink_two_eq[OF rel member]
    raw_unlink_two_preserves_index[OF rel member]
  by simp

lemma raw_remove_count_heap_preserves_index:
  assumes guard: "c_guard lp"
  shows
    "pxIndex_C (h_val (raw_remove_count_heap h lp) lp) =
     pxIndex_C (h_val h lp)"
  unfolding raw_remove_count_heap_def
  using guard by (simp add: h_val_heap_update)

lemma raw_remove_taken_index_heap_readback:
  assumes guard: "c_guard lp"
  shows
    "pxIndex_C (h_val (raw_remove_taken_index_heap h lp p) lp) =
     xLIST_ITEM_C.pxPrevious_C (h_val h p)"
  unfolding raw_remove_taken_index_heap_def
  using guard by (simp add: h_val_heap_update)

lemma raw_remove_taken_source_index_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "pxIndex_C
       (h_val
         (raw_remove_taken_suffix_heap (raw_source_unlink_two h p) lp p)
         lp) =
     raw_prev_at h lp p"
proof -
  let ?hu = "raw_source_unlink_two h p"
  let ?hi = "raw_remove_taken_index_heap ?hu lp p"
  let ?hc = "raw_remove_container_heap ?hi p"
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have guard: "c_guard lp"
    using layout by (simp add: raw_xlist_layout_def)
  have disjoint:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using layout member by (auto simp: raw_xlist_layout_def)
  have taken:
    "pxIndex_C (h_val ?hi lp) =
     xLIST_ITEM_C.pxPrevious_C (h_val ?hu p)"
    by (rule raw_remove_taken_index_heap_readback[OF guard])
  have item_same: "h_val ?hu p = h_val h p"
    by (rule raw_source_unlink_two_item_same[OF rel member])
  have previous:
    "xLIST_ITEM_C.pxPrevious_C (h_val ?hu p) = raw_prev_at h lp p"
    using item_same raw_full_previous_is_sentinel_safe[
      where h=h and u=p and lp=lp]
    by simp
  have container_list: "h_val ?hc lp = h_val ?hi lp"
    by (rule raw_remove_container_heap_preserves_list[OF disjoint])
  have count_index:
    "pxIndex_C (h_val (raw_remove_count_heap ?hc lp) lp) =
     pxIndex_C (h_val ?hc lp)"
    by (rule raw_remove_count_heap_preserves_index[OF guard])
  show ?thesis
    using taken previous container_list count_index
    by (simp add: raw_remove_taken_suffix_heap_def)
qed

lemma raw_remove_plain_source_index_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "pxIndex_C
       (h_val
         (raw_remove_plain_suffix_heap (raw_source_unlink_two h p) lp p)
         lp) =
     pxIndex_C (h_val h lp)"
proof -
  let ?hu = "raw_source_unlink_two h p"
  let ?hc = "raw_remove_container_heap ?hu p"
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have guard: "c_guard lp"
    using layout by (simp add: raw_xlist_layout_def)
  have disjoint:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using layout member by (auto simp: raw_xlist_layout_def)
  have unlink_index:
    "pxIndex_C (h_val ?hu lp) = pxIndex_C (h_val h lp)"
    by (rule raw_source_unlink_two_preserves_index[OF rel member])
  have container_list: "h_val ?hc lp = h_val ?hu lp"
    by (rule raw_remove_container_heap_preserves_list[OF disjoint])
  have count_index:
    "pxIndex_C (h_val (raw_remove_count_heap ?hc lp) lp) =
     pxIndex_C (h_val ?hc lp)"
    by (rule raw_remove_count_heap_preserves_index[OF guard])
  show ?thesis
    using unlink_index container_list count_index
    by (simp add: raw_remove_plain_suffix_heap_def)
qed

lemma raw_remove_concrete_heap_index_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "pxIndex_C (h_val (raw_remove_concrete_heap h p) lp) =
       (if pxIndex_C (h_val h lp) = p
        then raw_prev_at h lp p
        else pxIndex_C (h_val h lp))"
proof (cases "pxIndex_C (h_val h lp) = p")
  case True
  have cast:
    "PTR_COERCE(unit \<rightarrow> xLIST_C)
       (pvContainer_C (h_val (raw_source_unlink_two h p) p)) = lp"
    by (rule raw_source_unlink_two_container_cast[OF rel member])
  have unlink_index:
    "pxIndex_C (h_val (raw_source_unlink_two h p) lp) = p"
    using raw_source_unlink_two_preserves_index[OF rel member] True by simp
  have taken:
    "pxIndex_C
       (h_val
         (raw_remove_taken_suffix_heap (raw_source_unlink_two h p) lp p)
         lp) = raw_prev_at h lp p"
    by (rule raw_remove_taken_source_index_effect[OF rel member])
  show ?thesis
    using True cast unlink_index taken
    by (simp add: raw_remove_concrete_heap_def raw_remove_suffix_heap_def
        raw_remove_index_heap_def raw_remove_taken_index_heap_def
        raw_remove_taken_suffix_heap_def Let_def)
next
  case False
  have cast:
    "PTR_COERCE(unit \<rightarrow> xLIST_C)
       (pvContainer_C (h_val (raw_source_unlink_two h p) p)) = lp"
    by (rule raw_source_unlink_two_container_cast[OF rel member])
  have unlink_index:
    "pxIndex_C (h_val (raw_source_unlink_two h p) lp) \<noteq> p"
    using raw_source_unlink_two_preserves_index[OF rel member] False by simp
  have plain:
    "pxIndex_C
       (h_val
         (raw_remove_plain_suffix_heap (raw_source_unlink_two h p) lp p)
         lp) = pxIndex_C (h_val h lp)"
    by (rule raw_remove_plain_source_index_effect[OF rel member])
  show ?thesis
    using False cast unlink_index plain
    by (simp add: raw_remove_concrete_heap_def raw_remove_suffix_heap_def
        raw_remove_index_heap_def raw_remove_plain_suffix_heap_def Let_def)
qed

theorem raw_vListRemove_general_index_effect:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       pxIndex_C (h_val (hrs_mem (t_hrs_' t)) lp) =
         (if pxIndex_C (h_val (hrs_mem (t_hrs_' s)) lp) = p
          then raw_prev_at (hrs_mem (t_hrs_' s)) lp p
          else pxIndex_C (h_val (hrs_mem (t_hrs_' s)) lp))
     \<rbrace>"
proof -
  note heap_effect = raw_vListRemove_general_heap_effect[OF rel member]
  note index_effect = raw_remove_concrete_heap_index_effect[OF rel member]
  show ?thesis
    apply (rule runs_to_weaken[OF heap_effect])
    using index_effect
    by auto
qed

theorem raw_vListRemove_general_cursor_effect:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       raw_cursor_at (hrs_mem (t_hrs_' t)) lp =
         cursor (list_remove_abs p xs)
     \<rbrace>"
proof -
  note index_effect = raw_vListRemove_general_index_effect[OF rel member]
  show ?thesis
    apply (rule runs_to_weaken[OF index_effect])
    using raw_xlist_remove_cursor_transfer[OF rel member]
    by auto
qed

end
