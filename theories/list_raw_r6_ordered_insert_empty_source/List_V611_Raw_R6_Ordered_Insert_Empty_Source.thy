theory List_V611_Raw_R6_Ordered_Insert_Empty_Source
  imports
    "EAL6_FreeRTOS_V611_List_Raw_R6_Insert_Source_Effects.List_V611_Raw_R6_Insert_Source_Effects"
    "EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Index_Effect.List_V611_Raw_R6_Remove_Index_Effect"
begin

text \<open>
  Source-facing empty-list leaf for the stock ordered insertion routine.
  The sentinel key is deliberately layered over raw_xlist_rel: FIFO lists do
  not need this invariant, whereas ordered lists do.
\<close>

definition raw_sentinel_max ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> bool"
where
  "raw_sentinel_max h lp \<longleftrightarrow>
     raw_key_at h (raw_end_item lp) = (max_word :: 32 word)"

lemma raw_xlist_rel_empty_facts:
  assumes rel: "raw_xlist_rel h lp xs"
    and empty: "ring xs = []"
  shows
    "cursor xs = None \<and>
     uxNumberOfItems_C (h_val h lp) = 0 \<and>
     pxIndex_C (h_val h lp) = raw_end_item lp \<and>
     raw_next_at h lp (raw_end_item lp) = raw_end_item lp \<and>
     raw_prev_at h lp (raw_end_item lp) = raw_end_item lp"
proof -
  have wf: "xlist_wf xs"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have cursor_none: "cursor xs = None"
    using wf empty by (cases "cursor xs") (auto simp: xlist_wf_def)
  have count_unat:
    "unat (uxNumberOfItems_C (h_val h lp)) = 0"
    using raw_xlist_rel_countD[OF rel] empty by simp
  have count: "uxNumberOfItems_C (h_val h lp) = 0"
    using count_unat by (simp add: unat_eq_0)
  have index:
    "pxIndex_C (h_val h lp) = raw_end_item lp"
    using raw_xlist_rel_index_eq_cursor_node[OF rel] cursor_none
    by (simp add: raw_cursor_node_def)
  have links: "raw_ring_links h lp []"
    using rel empty
    by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have end_links:
    "raw_next_at h lp (raw_end_item lp) = raw_end_item lp \<and>
     raw_prev_at h lp (raw_end_item lp) = raw_end_item lp"
    using links by (simp add: raw_ring_links_empty_iff)
  show ?thesis using cursor_none count index end_links by blast
qed

lemma raw_ordered_empty_special_iterator:
  assumes rel: "raw_xlist_rel h lp xs"
    and empty: "ring xs = []"
  shows
    "xMINI_LIST_ITEM_C.pxPrevious_C (xListEnd_C (h_val h lp)) =
     raw_end_item lp"
  using raw_xlist_rel_empty_facts[OF rel empty]
  by simp

lemma raw_ordered_empty_source_next:
  assumes rel: "raw_xlist_rel h lp xs"
    and empty: "ring xs = []"
  shows
    "xLIST_ITEM_C.pxNext_C (h_val h (raw_end_item lp)) =
     raw_end_item lp"
proof -
  have raw_next:
    "raw_next_at h lp (raw_end_item lp) = raw_end_item lp"
    using raw_xlist_rel_empty_facts[OF rel empty] by blast
  show ?thesis
    using raw_full_next_is_sentinel_safe[
      where h = h and u = "raw_end_item lp" and lp = lp]
      raw_next by simp
qed

lemma raw_ordered_empty_loop_guard_false:
  assumes rel: "raw_xlist_rel h lp xs"
    and empty: "ring xs = []"
    and sentinel: "raw_sentinel_max h lp"
    and nonmax:
      "raw_key_at h p \<noteq> (max_word :: 32 word)"
  shows
    "\<not> (raw_key_at h
       (raw_next_at h lp (raw_end_item lp)) \<le> raw_key_at h p)"
proof -
  have next_eq:
    "raw_next_at h lp (raw_end_item lp) = raw_end_item lp"
    using raw_xlist_rel_empty_facts[OF rel empty] by blast
  show ?thesis
    using next_eq sentinel nonmax
    by (simp add: raw_sentinel_max_def)
qed

lemma raw_ordered_empty_source_loop_guard_false:
  assumes rel: "raw_xlist_rel h lp xs"
    and empty: "ring xs = []"
    and sentinel: "raw_sentinel_max h lp"
    and nonmax:
      "raw_key_at h p \<noteq> (max_word :: 32 word)"
  shows
    "\<not>
      (xLIST_ITEM_C.xItemValue_C
         (h_val h
           (xLIST_ITEM_C.pxNext_C
             (h_val h (raw_end_item lp))))
       \<le> xLIST_ITEM_C.xItemValue_C (h_val h p))"
proof -
  have false_guard:
    "\<not> (raw_key_at h
       (raw_next_at h lp (raw_end_item lp)) \<le> raw_key_at h p)"
    by (rule raw_ordered_empty_loop_guard_false[OF
          rel empty sentinel nonmax])
  have next_eq:
    "xLIST_ITEM_C.pxNext_C (h_val h (raw_end_item lp)) =
     raw_next_at h lp (raw_end_item lp)"
    by (rule raw_full_next_is_sentinel_safe)
  show ?thesis
    using false_guard next_eq by (simp add: raw_key_at_def)
qed

definition raw_ordered_insert_empty_heap ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow> heap_mem"
where
  "raw_ordered_insert_empty_heap h lp p =
     (let e = raw_end_item lp;
          h1 = raw_insert_next_heap h p e;
          h2 = raw_insert_previous_heap h1 e p;
          h3 = raw_insert_previous_heap h2 p e;
          h4 = raw_insert_next_heap h3 e p;
          h5 = raw_insert_container_heap h4 lp p
      in raw_insert_count_heap h5 lp)"

definition raw_ordered_empty_effect ::
  "heap_mem \<Rightarrow> heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow>
   raw_node_id \<Rightarrow> bool"
where
  "raw_ordered_empty_effect h h' lp p \<longleftrightarrow>
     uxNumberOfItems_C (h_val h' lp) = 1 \<and>
     pxIndex_C (h_val h' lp) = raw_end_item lp \<and>
     raw_ring_links h' lp [p] \<and>
     raw_key_at h' p = raw_key_at h p \<and>
     pvContainer_C (h_val h' p) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp \<and>
     raw_key_at h' (raw_end_item lp) =
       raw_key_at h (raw_end_item lp)"

lemma raw_ordered_fresh_previous_heap_preserves_list:
  assumes fresh: "raw_fresh_for_insert lp rs p"
  shows
    "h_val (raw_insert_previous_heap h p q) lp = h_val h lp"
proof -
  have item_list:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have field_list:
    "raw_pointer_field_region (raw_previous_field_ptr p) \<inter>
     raw_list_region lp = {}"
    using raw_previous_field_region_subset_item[where u=p] item_list
    by blast
  show ?thesis
    unfolding raw_insert_previous_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_list[OF
          field_list])
qed

lemma raw_ordered_end_next_heap_preserves_fresh_item:
  assumes fresh: "raw_fresh_for_insert lp rs p"
  shows
    "h_val
       (raw_insert_next_heap h (raw_end_item lp) v) p = h_val h p"
proof -
  have item_list:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have field_list:
    "raw_pointer_field_region
       (raw_next_field_ptr (raw_end_item lp)) \<subseteq>
     raw_list_region lp"
    by (rule raw_end_next_field_region_subset_list)
  have field_item:
    "raw_pointer_field_region
       (raw_next_field_ptr (raw_end_item lp)) \<inter>
     raw_item_region p = {}"
    using field_list item_list by blast
  show ?thesis
    unfolding raw_insert_next_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_item[OF
          field_item])
qed

lemma raw_ordered_end_previous_heap_preserves_fresh_item:
  assumes fresh: "raw_fresh_for_insert lp rs p"
  shows
    "h_val
       (raw_insert_previous_heap h (raw_end_item lp) v) p = h_val h p"
proof -
  have item_list:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have field_list:
    "raw_pointer_field_region
       (raw_previous_field_ptr (raw_end_item lp)) \<subseteq>
     raw_list_region lp"
    by (rule raw_end_previous_field_region_subset_list)
  have field_item:
    "raw_pointer_field_region
       (raw_previous_field_ptr (raw_end_item lp)) \<inter>
     raw_item_region p = {}"
    using field_list item_list by blast
  show ?thesis
    unfolding raw_insert_previous_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_item[OF
          field_item])
qed

lemma raw_ordered_list_update_preserves_fresh_item:
  assumes fresh: "raw_fresh_for_insert lp rs p"
  shows
    "h_val (heap_update lp (v :: xLIST_C) h) p = h_val h p"
proof -
  have disjoint:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have byte_disjoint:
    "{ptr_val lp..+
       length (to_bytes v
         (heap_list h (size_of TYPE(xLIST_C)) (ptr_val lp)))} \<inter>
     {ptr_val p..+size_of TYPE(xLIST_ITEM_C)} = {}"
    using disjoint
    by (simp add: raw_list_region_def raw_item_region_def Int_commute)
  have heap_lists_same:
    "heap_list
       (heap_update_list (ptr_val lp)
         (to_bytes v
           (heap_list h (size_of TYPE(xLIST_C)) (ptr_val lp))) h)
       (size_of TYPE(xLIST_ITEM_C)) (ptr_val p) =
     heap_list h (size_of TYPE(xLIST_ITEM_C)) (ptr_val p)"
    by (rule heap_list_update_disjoint_same[OF byte_disjoint])
  show ?thesis
    unfolding h_val_def heap_update_def
    using heap_lists_same by simp
qed

lemma raw_ordered_sentinel_key_cong:
  assumes list_same: "h_val h' lp = h_val h lp"
  shows
    "raw_key_at h' (raw_end_item lp) =
     raw_key_at h (raw_end_item lp)"
  using raw_sentinel_item_value_prefix_generic[where h=h' and lp=lp]
    raw_sentinel_item_value_prefix_generic[where h=h and lp=lp]
    list_same
  by (simp add: raw_key_at_def raw_end_item_def)

lemma raw_ordered_insert_empty_transformer_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and empty: "ring xs = []"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "raw_ordered_empty_effect h
       (raw_ordered_insert_empty_heap h lp p) lp p"
proof -
  let ?e = "raw_end_item lp"
  let ?h1 = "raw_insert_next_heap h p ?e"
  let ?h2 = "raw_insert_previous_heap ?h1 ?e p"
  let ?h3 = "raw_insert_previous_heap ?h2 p ?e"
  let ?h4 = "raw_insert_next_heap ?h3 ?e p"
  let ?h5 = "raw_insert_container_heap ?h4 lp p"
  let ?h6 = "raw_insert_count_heap ?h5 lp"
  have layout: "raw_xlist_layout lp []"
    using rel empty by (simp add: raw_xlist_rel_def)
  have p_guard: "c_guard p"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have lp_guard: "c_guard lp"
    using layout by (simp add: raw_xlist_layout_def)
  have e_guard: "c_guard ?e"
    using layout by (simp add: raw_xlist_layout_def)
  have p_ne_e: "p \<noteq> ?e"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have item_list:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using fresh by (simp add: raw_fresh_for_insert_def)
  note empty_facts = raw_xlist_rel_empty_facts[OF rel empty]

  have h1_list: "h_val ?h1 lp = h_val h lp"
    by (rule raw_insert_next_heap_preserves_list[OF fresh])
  have h2_count:
    "uxNumberOfItems_C (h_val ?h2 lp) =
     uxNumberOfItems_C (h_val ?h1 lp)"
    unfolding raw_insert_previous_heap_def
    by (rule raw_previous_field_update_preserves_count[OF layout]) simp
  have h2_index:
    "pxIndex_C (h_val ?h2 lp) = pxIndex_C (h_val ?h1 lp)"
    unfolding raw_insert_previous_heap_def
    by (rule raw_previous_field_update_preserves_index[OF layout]) simp
  have h3_list: "h_val ?h3 lp = h_val ?h2 lp"
    by (rule raw_ordered_fresh_previous_heap_preserves_list[OF fresh])
  have h4_count:
    "uxNumberOfItems_C (h_val ?h4 lp) =
     uxNumberOfItems_C (h_val ?h3 lp)"
    unfolding raw_insert_next_heap_def
    by (rule raw_next_field_update_preserves_count[OF layout]) simp
  have h4_index:
    "pxIndex_C (h_val ?h4 lp) = pxIndex_C (h_val ?h3 lp)"
    unfolding raw_insert_next_heap_def
    by (rule raw_next_field_update_preserves_index[OF layout]) simp
  have h5_list: "h_val ?h5 lp = h_val ?h4 lp"
    unfolding raw_insert_container_heap_def
    by (rule raw_item_update_preserves_disjoint_list[OF item_list])
  have h6_count:
    "uxNumberOfItems_C (h_val ?h6 lp) =
     uxNumberOfItems_C (h_val ?h5 lp) + 1"
    unfolding raw_insert_count_heap_def
    using lp_guard by (simp add: h_val_heap_update)
  have h6_index:
    "pxIndex_C (h_val ?h6 lp) = pxIndex_C (h_val ?h5 lp)"
    unfolding raw_insert_count_heap_def
    using lp_guard by (simp add: h_val_heap_update)
  have final_count: "uxNumberOfItems_C (h_val ?h6 lp) = 1"
    using empty_facts h1_list h2_count h3_list h4_count h5_list h6_count
    by simp
  have final_index: "pxIndex_C (h_val ?h6 lp) = ?e"
    using empty_facts h1_list h2_index h3_list h4_index h5_list h6_index
    by simp

  have h1_item:
    "xLIST_ITEM_C.pxNext_C (h_val ?h1 p) = ?e \<and>
     raw_key_at ?h1 p = raw_key_at h p"
    unfolding raw_insert_next_heap_def
    using raw_next_field_update_to_whole[
        OF p_guard, where q = ?e and h = h]
      p_guard
    by (simp add: raw_key_at_def h_val_heap_update)
  have h2_item: "h_val ?h2 p = h_val ?h1 p"
    by (rule raw_ordered_end_previous_heap_preserves_fresh_item[OF fresh])
  have h3_whole:
    "?h3 =
     heap_update p
       (xLIST_ITEM_C.pxPrevious_C_update (\<lambda>_. ?e)
         (h_val ?h2 p)) ?h2"
    unfolding raw_insert_previous_heap_def
    by (rule raw_previous_field_update_to_whole[OF p_guard])
  have h3_item:
    "xLIST_ITEM_C.pxNext_C (h_val ?h3 p) =
       xLIST_ITEM_C.pxNext_C (h_val ?h2 p) \<and>
     xLIST_ITEM_C.pxPrevious_C (h_val ?h3 p) = ?e \<and>
     raw_key_at ?h3 p = raw_key_at ?h2 p"
    using h3_whole p_guard
    by (simp add: raw_key_at_def h_val_heap_update)
  have h4_item: "h_val ?h4 p = h_val ?h3 p"
    by (rule raw_ordered_end_next_heap_preserves_fresh_item[OF fresh])
  have h4_whole:
    "?h4 =
     heap_update ?e
       (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. p)
         (h_val ?h3 ?e)) ?h3"
    unfolding raw_insert_next_heap_def
    by (rule raw_next_field_update_to_whole[OF e_guard])
  have h5_item:
    "xLIST_ITEM_C.pxNext_C (h_val ?h5 p) =
       xLIST_ITEM_C.pxNext_C (h_val ?h4 p) \<and>
     xLIST_ITEM_C.pxPrevious_C (h_val ?h5 p) =
       xLIST_ITEM_C.pxPrevious_C (h_val ?h4 p) \<and>
     raw_key_at ?h5 p = raw_key_at ?h4 p \<and>
     pvContainer_C (h_val ?h5 p) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    unfolding raw_insert_container_heap_def
    using p_guard
    by (simp add: raw_key_at_def h_val_heap_update)
  have h6_item: "h_val ?h6 p = h_val ?h5 p"
    unfolding raw_insert_count_heap_def
    by (rule raw_ordered_list_update_preserves_fresh_item[OF fresh])
  have final_item:
    "xLIST_ITEM_C.pxNext_C (h_val ?h6 p) = ?e \<and>
     xLIST_ITEM_C.pxPrevious_C (h_val ?h6 p) = ?e \<and>
     raw_key_at ?h6 p = raw_key_at h p \<and>
     pvContainer_C (h_val ?h6 p) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    using h1_item h2_item h3_item h4_item h5_item h6_item
    by (simp add: raw_key_at_def)

  have h2_end_previous: "raw_prev_at ?h2 lp ?e = p"
    unfolding raw_insert_previous_heap_def
    by (rule raw_prev_at_after_same_node_previous_field_update[OF e_guard])
  have h3_end_previous: "raw_prev_at ?h3 lp ?e = p"
    using h3_list h2_end_previous by simp
  have h4_end:
    "raw_next_at ?h4 lp ?e = p \<and>
     raw_prev_at ?h4 lp ?e = p"
  proof
    show "raw_next_at ?h4 lp ?e = p"
      unfolding raw_insert_next_heap_def
      by (rule raw_next_at_after_same_node_next_field_update[OF e_guard])
    show "raw_prev_at ?h4 lp ?e = p"
    proof -
      have frame:
        "raw_prev_at ?h4 lp ?e = raw_prev_at ?h3 lp ?e"
        unfolding raw_insert_next_heap_def
        by (rule raw_prev_at_survives_same_node_next_field_update[
              OF e_guard])
      show ?thesis using frame h3_end_previous by simp
    qed
  qed
  have h5_end:
    "raw_next_at ?h5 lp ?e = p \<and>
     raw_prev_at ?h5 lp ?e = p"
    using h5_list h4_end by simp
  have h6_end:
    "raw_next_at ?h6 lp ?e = p \<and>
     raw_prev_at ?h6 lp ?e = p"
    unfolding raw_insert_count_heap_def raw_next_at_def raw_prev_at_def
    using lp_guard h5_end
    by (simp add: h_val_heap_update)
  have final_links: "raw_ring_links ?h6 lp [p]"
    using raw_ring_links_singleton_iff[OF p_ne_e, where h = ?h6]
      final_item h6_end p_ne_e
    by (simp add: raw_next_at_def raw_prev_at_def)

  have h1_sentinel_key:
    "raw_key_at ?h1 ?e = raw_key_at h ?e"
    by (rule raw_ordered_sentinel_key_cong[OF h1_list])
  have h2_sentinel_key:
    "raw_key_at ?h2 ?e = raw_key_at ?h1 ?e"
    unfolding raw_insert_previous_heap_def
    using raw_previous_field_update_to_whole[
        OF e_guard, where q = p and h = ?h1]
      e_guard
    by (simp add: raw_key_at_def h_val_heap_update)
  have h3_sentinel_key:
    "raw_key_at ?h3 ?e = raw_key_at ?h2 ?e"
    by (rule raw_ordered_sentinel_key_cong[OF h3_list])
  have h4_sentinel_key:
    "raw_key_at ?h4 ?e = raw_key_at ?h3 ?e"
    using h4_whole e_guard
    by (simp add: raw_key_at_def h_val_heap_update)
  have h5_sentinel_key:
    "raw_key_at ?h5 ?e = raw_key_at ?h4 ?e"
    by (rule raw_ordered_sentinel_key_cong[OF h5_list])
  have h6_sentinel_key:
    "raw_key_at ?h6 ?e = raw_key_at ?h5 ?e"
  proof -
    have list_value:
      "h_val ?h6 lp =
       uxNumberOfItems_C_update (\<lambda>n. n + 1) (h_val ?h5 lp)"
      unfolding raw_insert_count_heap_def
      using lp_guard by (simp add: h_val_heap_update)
    show ?thesis
      using raw_sentinel_item_value_prefix_generic[
          where h = ?h6 and lp = lp]
        raw_sentinel_item_value_prefix_generic[
          where h = ?h5 and lp = lp]
        list_value
      by (simp add: raw_key_at_def raw_end_item_def)
  qed
  have final_sentinel_key:
    "raw_key_at ?h6 ?e = raw_key_at h ?e"
    using h1_sentinel_key h2_sentinel_key h3_sentinel_key
      h4_sentinel_key h5_sentinel_key h6_sentinel_key by simp

  show ?thesis
    using final_count final_index final_links final_item final_sentinel_key
    by (simp add: raw_ordered_empty_effect_def
        raw_ordered_insert_empty_heap_def Let_def)
qed

theorem raw_vListInsert_ordered_empty_max_heap_effect:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and empty: "ring xs = []"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and key_max:
      "raw_key_at (hrs_mem (t_hrs_' s)) p =
       (max_word :: 32 word)"
  shows
    "vListInsert' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       hrs_mem (t_hrs_' t) =
         raw_ordered_insert_empty_heap
           (hrs_mem (t_hrs_' s)) lp p
     \<rbrace>"
proof -
  let ?h = "hrs_mem (t_hrs_' s)"
  let ?e = "raw_end_item lp"
  have p_guard: "c_guard p"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have lp_guard: "c_guard lp"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_layout_def)
  have e_guard: "c_guard ?e"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_layout_def)
  have key_value:
    "xLIST_ITEM_C.xItemValue_C (h_val ?h p) = 0xFFFFFFFF"
    using key_max by (simp add: raw_key_at_def)
  have iterator:
    "xMINI_LIST_ITEM_C.pxPrevious_C (xListEnd_C (h_val ?h lp)) = ?e"
    by (rule raw_ordered_empty_special_iterator[OF rel empty])
  have end_next:
    "xLIST_ITEM_C.pxNext_C (h_val ?h ?e) = ?e"
    by (rule raw_ordered_empty_source_next[OF rel empty])
  show ?thesis
    unfolding vListInsert'_def
    apply runs_to_vcg
    apply (simp_all only: hrs_mem_update key_value iterator end_next)
    apply (simp_all add: h_val_heap_update p_guard lp_guard e_guard)
    apply (simp_all only:
        raw_next_field_update_to_whole[OF p_guard, symmetric]
        raw_previous_field_update_to_whole[OF p_guard, symmetric]
        raw_next_field_update_to_whole[OF e_guard, symmetric])
    apply (fold raw_previous_field_ptr_def)
    apply (fold raw_insert_next_heap_def raw_insert_previous_heap_def)
    apply (fold raw_insert_container_heap_def raw_insert_count_heap_def)
    apply (simp_all add: raw_ordered_insert_empty_heap_def Let_def)
    done
qed

theorem raw_vListInsert_ordered_empty_nonmax_heap_effect:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and empty: "ring xs = []"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and sentinel:
      "raw_sentinel_max (hrs_mem (t_hrs_' s)) lp"
    and key_nonmax:
      "raw_key_at (hrs_mem (t_hrs_' s)) p \<noteq>
       (max_word :: 32 word)"
  shows
    "vListInsert' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       hrs_mem (t_hrs_' t) =
         raw_ordered_insert_empty_heap
           (hrs_mem (t_hrs_' s)) lp p
     \<rbrace>"
proof -
  let ?h = "hrs_mem (t_hrs_' s)"
  let ?e = "raw_end_item lp"
  have p_guard: "c_guard p"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have lp_guard: "c_guard lp"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_layout_def)
  have e_guard: "c_guard ?e"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_layout_def)
  have hex_max:
    "(0xFFFFFFFF :: 32 word) = (max_word :: 32 word)"
    by simp
  have key_nonvalue:
    "xLIST_ITEM_C.xItemValue_C (h_val ?h p) \<noteq> 0xFFFFFFFF"
    apply (subst hex_max)
    using key_nonmax by (simp add: raw_key_at_def)
  have sentinel_ptr:
    "PTR(xLIST_ITEM_C) &(lp\<rightarrow>[''xListEnd_C'']) = ?e"
    by (simp add: raw_end_item_def raw_sentinel_ptr_def)
  have end_next:
    "xLIST_ITEM_C.pxNext_C (h_val ?h ?e) = ?e"
    by (rule raw_ordered_empty_source_next[OF rel empty])
  have loop_false:
    "\<not>
      (xLIST_ITEM_C.xItemValue_C
         (h_val ?h
           (xLIST_ITEM_C.pxNext_C (h_val ?h ?e)))
       \<le> xLIST_ITEM_C.xItemValue_C (h_val ?h p))"
    by (rule raw_ordered_empty_source_loop_guard_false[OF
          rel empty sentinel key_nonmax])
  show ?thesis
    unfolding vListInsert'_def
    apply runs_to_vcg
    apply (simp_all only:
        hrs_mem_update key_nonvalue sentinel_ptr end_next loop_false)
    apply (simp_all add: h_val_heap_update p_guard lp_guard e_guard)
    apply (subst runs_to_whileLoop_cond_fail)
     apply (rule loop_false)
    apply runs_to_vcg
    apply (simp_all only: hrs_mem_update end_next)
    apply (simp_all add: h_val_heap_update p_guard lp_guard e_guard)
    apply (simp_all only:
        raw_next_field_update_to_whole[OF p_guard, symmetric]
        raw_previous_field_update_to_whole[OF p_guard, symmetric]
        raw_next_field_update_to_whole[OF e_guard, symmetric])
    apply (fold raw_previous_field_ptr_def)
    apply (fold raw_insert_next_heap_def raw_insert_previous_heap_def)
    apply (fold raw_insert_container_heap_def raw_insert_count_heap_def)
    apply (simp_all add: raw_ordered_insert_empty_heap_def Let_def)
    done
qed

theorem raw_vListInsert_ordered_empty_heap_effect:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and empty: "ring xs = []"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and sentinel:
      "raw_sentinel_max (hrs_mem (t_hrs_' s)) lp"
  shows
    "vListInsert' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       hrs_mem (t_hrs_' t) =
         raw_ordered_insert_empty_heap
           (hrs_mem (t_hrs_' s)) lp p
     \<rbrace>"
proof (cases
    "raw_key_at (hrs_mem (t_hrs_' s)) p =
     (max_word :: 32 word)")
  case True
  show ?thesis
    by (rule raw_vListInsert_ordered_empty_max_heap_effect[OF
          rel empty fresh True])
next
  case False
  show ?thesis
    by (rule raw_vListInsert_ordered_empty_nonmax_heap_effect[OF
          rel empty fresh sentinel False])
qed

end
