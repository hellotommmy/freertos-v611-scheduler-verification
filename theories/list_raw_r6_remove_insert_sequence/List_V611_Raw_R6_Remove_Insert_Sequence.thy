theory List_V611_Raw_R6_Remove_Insert_Sequence
  imports
    "EAL6_FreeRTOS_V611_List_Raw_R6_Remove_General_Refinement.List_V611_Raw_R6_Remove_General_Refinement"
    "EAL6_FreeRTOS_V611_List_Raw_R6_Insert_Post_Transformer.List_V611_Raw_R6_Insert_Post_Transformer"
begin

text \<open>
  General-N sequential needle: remove one live item and insert that same item
  at the current list cursor.  No generated C body is reopened here.  The
  proof composes the checked exact-remove heap certificate, the checked
  general remove refinement, and the checked general insert refinement.
\<close>

lemma raw_remove_index_heap_preserves_member_item:
  assumes layout: "raw_xlist_layout lp rs"
    and member: "p \<in> set rs"
  shows "h_val (raw_remove_index_heap h lp p) p = h_val h p"
proof (cases "pxIndex_C (h_val h lp) = p")
  case True
  have same:
    "h_val
       (heap_update lp
         (pxIndex_C_update
           (\<lambda>_. xLIST_ITEM_C.pxPrevious_C (h_val h p))
           (h_val h lp)) h) p = h_val h p"
    by (rule
      List_V611_Raw_R6_Remove_Payload_Effect.raw_layout_list_update_preserves_live_item[
        OF layout member])
  show ?thesis
    using True same by (simp add: raw_remove_index_heap_def)
next
  case False
  then show ?thesis by (simp add: raw_remove_index_heap_def)
qed

lemma raw_remove_count_heap_preserves_member_item:
  assumes layout: "raw_xlist_layout lp rs"
    and member: "p \<in> set rs"
  shows "h_val (raw_remove_count_heap h lp) p = h_val h p"
  unfolding raw_remove_count_heap_def
  by (rule
    List_V611_Raw_R6_Remove_Payload_Effect.raw_layout_list_update_preserves_live_item[
      OF layout member])

lemma raw_remove_container_heap_preserves_item_key:
  assumes guard: "c_guard p"
  shows
    "raw_key_at (raw_remove_container_heap h p) p = raw_key_at h p"
  unfolding raw_remove_container_heap_def raw_key_at_def
  using guard by (simp add: h_val_heap_update)

lemma raw_remove_source_heap_preserves_item_key:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_key_at (raw_remove_source_heap h lp p) p = raw_key_at h p"
proof -
  let ?hu = "raw_source_unlink_two h p"
  let ?hi = "raw_remove_index_heap ?hu lp p"
  let ?hc = "raw_remove_container_heap ?hi p"
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have guard: "c_guard p"
    using layout member by (auto simp: raw_xlist_layout_def)
  have unlink_same: "h_val ?hu p = h_val h p"
    by (rule raw_source_unlink_two_item_same[OF rel member])
  have index_same: "h_val ?hi p = h_val ?hu p"
    by (rule raw_remove_index_heap_preserves_member_item[
          OF layout member])
  have container_key: "raw_key_at ?hc p = raw_key_at ?hi p"
    by (rule raw_remove_container_heap_preserves_item_key[OF guard])
  have count_same:
    "h_val (raw_remove_count_heap ?hc lp) p = h_val ?hc p"
    by (rule raw_remove_count_heap_preserves_member_item[
          OF layout member])
  show ?thesis
    using unlink_same index_same container_key count_same
    by (simp add: raw_remove_source_heap_def raw_remove_suffix_heap_def
        raw_key_at_def)
qed

lemma raw_remove_concrete_heap_preserves_item_key:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_key_at (raw_remove_concrete_heap h p) p = raw_key_at h p"
  using raw_remove_concrete_heap_eq[OF rel member]
    raw_remove_source_heap_preserves_item_key[OF rel member]
  by simp

lemma raw_remove_post_fresh_for_insert:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_fresh_for_insert lp (ring (list_remove_abs p xs)) p"
proof -
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have distinct: "distinct (ring xs)"
    using raw_xlist_rel_distinct_cycle_nodes[OF rel] by simp
  have not_remaining: "p \<notin> set (remove1 p (ring xs))"
    by (rule raw_distinct_member_notin_remove1[OF distinct member])
  have guard: "c_guard p"
    using layout member by (auto simp: raw_xlist_layout_def)
  have not_end: "p \<noteq> raw_end_item lp"
    using layout member by (auto simp: raw_xlist_layout_def)
  have item_list:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using layout member by (auto simp: raw_xlist_layout_def)
  have item_items:
    "\<forall>q \<in> set (remove1 p (ring xs)).
       raw_item_region p \<inter> raw_item_region q = {}"
  proof (intro ballI)
    fix q
    assume remaining: "q \<in> set (remove1 p (ring xs))"
    have old: "q \<in> set (ring xs)"
      by (rule subsetD[OF set_remove1_subset remaining])
    have different: "p \<noteq> q"
      using not_remaining remaining by auto
    show "raw_item_region p \<inter> raw_item_region q = {}"
      using layout member old different
      by (auto simp: raw_xlist_layout_def)
  qed
  show ?thesis
    using guard not_end not_remaining item_list item_items
    by (simp add: raw_fresh_for_insert_def list_remove_abs_def)
qed

lemma raw_remove_post_count_can_increment:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows "raw_count_can_increment (list_remove_abs p xs)"
proof -
  let ?w = "uxNumberOfItems_C (h_val h lp)"
  have count: "unat ?w = length (ring xs)"
    by (rule raw_xlist_rel_countD[OF rel])
  have positive: "0 < length (ring xs)"
    using member by auto
  have removed_lt:
    "length (remove1 p (ring xs)) < length (ring xs)"
    using member positive by (simp add: length_remove1)
  have word_bound: "?w \<le> (max_word :: 32 word)"
    by (rule word_order.extremum)
  have old_length_bound:
    "length (ring xs) \<le> unat (max_word :: 32 word)"
    using count word_bound by (simp add: word_le_nat_alt)
  have removed_bound:
    "length (remove1 p (ring xs)) < unat (max_word :: 32 word)"
    by (rule order_less_le_trans[OF removed_lt old_length_bound])
  show ?thesis
    using removed_bound
    by (simp add: raw_count_can_increment_def list_remove_abs_def)
qed

theorem raw_vListRemove_general_sequence_ready:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       raw_xlist_rel (hrs_mem (t_hrs_' t)) lp
         (list_remove_abs p xs) \<and>
       hrs_mem (t_hrs_' t) =
         raw_remove_concrete_heap (hrs_mem (t_hrs_' s)) p \<and>
       raw_fresh_for_insert lp (ring (list_remove_abs p xs)) p \<and>
       raw_count_can_increment (list_remove_abs p xs) \<and>
       raw_key_at (hrs_mem (t_hrs_' t)) p =
         raw_key_at (hrs_mem (t_hrs_' s)) p
     \<rbrace>"
proof -
  note refinement = raw_vListRemove_general_refines[OF rel member]
  note heap = raw_vListRemove_general_heap_effect[OF rel member]
  have grouped:
    "vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r t.
       (r = Result () \<and>
        raw_xlist_rel (hrs_mem (t_hrs_' t)) lp
          (list_remove_abs p xs)) \<and>
       (r = Result () \<and>
        hrs_mem (t_hrs_' t) =
          raw_remove_concrete_heap (hrs_mem (t_hrs_' s)) p)
     \<rbrace>"
    using refinement heap by (simp only: runs_to_conj)
  have fresh:
    "raw_fresh_for_insert lp (ring (list_remove_abs p xs)) p"
    by (rule raw_remove_post_fresh_for_insert[OF rel member])
  have can_increment:
    "raw_count_can_increment (list_remove_abs p xs)"
    by (rule raw_remove_post_count_can_increment[OF rel member])
  have key:
    "raw_key_at
       (raw_remove_concrete_heap (hrs_mem (t_hrs_' s)) p) p =
     raw_key_at (hrs_mem (t_hrs_' s)) p"
    by (rule raw_remove_concrete_heap_preserves_item_key[OF rel member])
  show ?thesis
    apply (rule runs_to_weaken[OF grouped])
    using fresh can_increment key by auto
qed

lemma raw_vListInsertEnd_sequence_continuation:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' t)) lp ys"
    and fresh: "raw_fresh_for_insert lp (ring ys) p"
    and can_increment: "raw_count_can_increment ys"
    and key: "raw_key_at (hrs_mem (t_hrs_' t)) p = k"
  shows
    "vListInsertEnd' lp p \<bullet> t
     \<lbrace>\<lambda>r u.
       r = Result () \<and>
       raw_xlist_rel (hrs_mem (t_hrs_' u)) lp
         (list_insert_end_abs p k ys)
     \<rbrace>"
proof -
  note insert = raw_vListInsertEnd_general_refines_via_transformer[
    OF rel fresh can_increment]
  show ?thesis
    apply (rule runs_to_weaken[OF insert])
    using key by simp
qed

lemma raw_vListInsertEnd_sequence_continuation_res:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' t)) lp ys"
    and fresh: "raw_fresh_for_insert lp (ring ys) p"
    and can_increment: "raw_count_can_increment ys"
    and key: "raw_key_at (hrs_mem (t_hrs_' t)) p = k"
  shows
    "vListInsertEnd' lp p \<bullet> t
     \<lbrace>\<lambda>Res _ u.
       raw_xlist_rel (hrs_mem (t_hrs_' u)) lp
         (list_insert_end_abs p k ys)
     \<rbrace>"
proof -
  note strong = raw_vListInsertEnd_sequence_continuation[
    OF rel fresh can_increment key]
  show ?thesis
    apply (rule runs_to_weaken[OF strong])
    by auto
qed

theorem raw_vListRemove_insert_end_general_refines:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "bind (vListRemove' p) (\<lambda>_. vListInsertEnd' lp p) \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       raw_xlist_rel (hrs_mem (t_hrs_' t)) lp
         (list_insert_end_abs p
           (raw_key_at (hrs_mem (t_hrs_' s)) p)
           (list_remove_abs p xs))
     \<rbrace>"
proof -
  note ready = raw_vListRemove_general_sequence_ready[OF rel member]
  show ?thesis
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF ready])
    apply clarsimp
    apply (rule runs_to_weaken[OF
          raw_vListInsertEnd_sequence_continuation])
    apply simp_all
    done
qed

end
