theory List_V611_Raw_R6_Ordered_Insert_Empty_Refinement
  imports
    "EAL6_FreeRTOS_V611_List_Raw_R6_Ordered_Insert_Empty_Source.List_V611_Raw_R6_Ordered_Insert_Empty_Source"
    "EAL6_FreeRTOS_V611_List_Raw_R6_Insert_Post_Transformer.List_V611_Raw_R6_Insert_Post_Transformer"
begin

text \<open>
  Relation projection for the empty-list branch of stock vListInsert.  The
  source leaf owns the exact heap transformer and the source certificate;
  this leaf only assembles the resulting observations into the abstract
  ordered insertion relation.  In particular, no source body is reopened.
\<close>

lemma raw_xlist_rel_ordered_empty_insertI:
  assumes rel: "raw_xlist_rel h lp xs"
    and empty: "ring xs = []"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and count: "uxNumberOfItems_C (h_val h' lp) = 1"
    and index: "pxIndex_C (h_val h' lp) = raw_end_item lp"
    and links: "raw_ring_links h' lp [p]"
    and key: "raw_key_at h' p = k"
    and container:
      "pvContainer_C (h_val h' p) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
  shows
    "raw_xlist_rel h' lp (list_insert_ordered_abs p k xs)"
proof -
  let ?ys = "list_insert_ordered_abs p k xs"
  have old_wf: "xlist_wf xs"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have p_fresh: "p \<notin> set (ring xs)"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have new_wf: "xlist_wf ?ys"
    by (rule list_insert_ordered_preserves_wf[OF old_wf p_fresh])
  have cursor_none: "cursor xs = None"
    using old_wf empty
    by (cases "cursor xs") (auto simp: xlist_wf_def)
  have new_ring: "ring ?ys = [p]"
    using empty by (simp add: list_insert_ordered_abs_def)
  have new_cursor: "cursor ?ys = None"
    using cursor_none by (simp add: list_insert_ordered_abs_def Let_def)
  have new_key: "item_key ?ys p = k"
    by (simp add: list_insert_ordered_abs_def Let_def)
  have old_layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have new_layout: "raw_xlist_layout lp (ring ?ys)"
  proof (rule raw_xlist_layout_extend_set[OF old_layout fresh])
    show "set (ring ?ys) = insert p (set (ring xs))"
      using new_ring empty by simp
  qed
  show ?thesis
    unfolding raw_xlist_rel_def
  proof (intro conjI)
    show "raw_xlist_layout lp (ring ?ys)"
      by (rule new_layout)
    show "raw_xlist_view h' lp ?ys"
      unfolding raw_xlist_view_def
    proof (intro conjI)
      show "xlist_wf ?ys"
        by (rule new_wf)
      show
        "unat (uxNumberOfItems_C (h_val h' lp)) = length (ring ?ys)"
        using count new_ring by simp
      show "cursor ?ys = raw_cursor_at h' lp"
        using new_cursor index by (simp add: raw_cursor_at_def)
      show "raw_ring_links h' lp (ring ?ys)"
        using links new_ring by simp
      show
        "\<forall>q \<in> set (ring ?ys).
          item_key ?ys q = raw_key_at h' q \<and>
          pvContainer_C (h_val h' q) =
            PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
      proof (intro ballI)
        fix q
        assume q_live: "q \<in> set (ring ?ys)"
        have q_eq: "q = p"
          using q_live new_ring by simp
        show
          "item_key ?ys q = raw_key_at h' q \<and>
           pvContainer_C (h_val h' q) =
             PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
          using q_eq new_key key container by simp
      qed
    qed
  qed
qed

lemma raw_ordered_empty_effect_refines:
  assumes rel: "raw_xlist_rel h lp xs"
    and empty: "ring xs = []"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and effect: "raw_ordered_empty_effect h h' lp p"
  shows
    "raw_xlist_rel h' lp
       (list_insert_ordered_abs p (raw_key_at h p) xs)"
proof -
  have count: "uxNumberOfItems_C (h_val h' lp) = 1"
    using effect by (simp add: raw_ordered_empty_effect_def)
  have index: "pxIndex_C (h_val h' lp) = raw_end_item lp"
    using effect by (simp add: raw_ordered_empty_effect_def)
  have links: "raw_ring_links h' lp [p]"
    using effect by (simp add: raw_ordered_empty_effect_def)
  have key: "raw_key_at h' p = raw_key_at h p"
    using effect by (simp add: raw_ordered_empty_effect_def)
  have container:
    "pvContainer_C (h_val h' p) =
     PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    using effect by (simp add: raw_ordered_empty_effect_def)
  show ?thesis
    by (rule raw_xlist_rel_ordered_empty_insertI[
          OF rel empty fresh count index links key container])
qed

theorem raw_ordered_insert_empty_transformer_refines:
  assumes rel: "raw_xlist_rel h lp xs"
    and empty: "ring xs = []"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "raw_xlist_rel (raw_ordered_insert_empty_heap h lp p) lp
       (list_insert_ordered_abs p (raw_key_at h p) xs)"
proof -
  have effect:
    "raw_ordered_empty_effect h
       (raw_ordered_insert_empty_heap h lp p) lp p"
    by (rule raw_ordered_insert_empty_transformer_effect[
          OF rel empty fresh])
  show ?thesis
    by (rule raw_ordered_empty_effect_refines[
          OF rel empty fresh effect])
qed

definition raw_ordered_xlist_rel ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow> bool"
where
  "raw_ordered_xlist_rel h lp xs \<longleftrightarrow>
     raw_xlist_rel h lp xs \<and>
     raw_sentinel_max h lp \<and>
     sorted (map (item_key xs) (ring xs))"

lemma raw_ordered_xlist_rel_emptyI:
  assumes rel: "raw_xlist_rel h lp xs"
    and sentinel: "raw_sentinel_max h lp"
    and empty: "ring xs = []"
  shows "raw_ordered_xlist_rel h lp xs"
  using rel sentinel empty
  by (simp add: raw_ordered_xlist_rel_def)

lemma raw_ordered_empty_effect_refines_ordered:
  assumes ordered: "raw_ordered_xlist_rel h lp xs"
    and empty: "ring xs = []"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and effect: "raw_ordered_empty_effect h h' lp p"
  shows
    "raw_ordered_xlist_rel h' lp
       (list_insert_ordered_abs p (raw_key_at h p) xs)"
proof -
  have rel: "raw_xlist_rel h lp xs"
    using ordered by (simp add: raw_ordered_xlist_rel_def)
  have sentinel: "raw_sentinel_max h lp"
    using ordered by (simp add: raw_ordered_xlist_rel_def)
  have refined:
    "raw_xlist_rel h' lp
       (list_insert_ordered_abs p (raw_key_at h p) xs)"
    by (rule raw_ordered_empty_effect_refines[OF rel empty fresh effect])
  have sentinel_frame:
    "raw_key_at h' (raw_end_item lp) =
     raw_key_at h (raw_end_item lp)"
    using effect by (simp add: raw_ordered_empty_effect_def)
  have final_sentinel: "raw_sentinel_max h' lp"
    using sentinel sentinel_frame by (simp add: raw_sentinel_max_def)
  have sorted_post:
    "sorted
       (map
         (item_key
           (list_insert_ordered_abs p (raw_key_at h p) xs))
         (ring
           (list_insert_ordered_abs p (raw_key_at h p) xs)))"
    using empty by (simp add: list_insert_ordered_abs_def)
  show ?thesis
    using refined final_sentinel sorted_post
    by (simp add: raw_ordered_xlist_rel_def)
qed

theorem raw_ordered_insert_empty_transformer_refines_ordered:
  assumes ordered: "raw_ordered_xlist_rel h lp xs"
    and empty: "ring xs = []"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "raw_ordered_xlist_rel (raw_ordered_insert_empty_heap h lp p) lp
       (list_insert_ordered_abs p (raw_key_at h p) xs)"
proof -
  have rel: "raw_xlist_rel h lp xs"
    using ordered by (simp add: raw_ordered_xlist_rel_def)
  have effect:
    "raw_ordered_empty_effect h
       (raw_ordered_insert_empty_heap h lp p) lp p"
    by (rule raw_ordered_insert_empty_transformer_effect[
          OF rel empty fresh])
  show ?thesis
    by (rule raw_ordered_empty_effect_refines_ordered[
          OF ordered empty fresh effect])
qed

theorem raw_vListInsert_ordered_empty_refines:
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
       raw_xlist_rel (hrs_mem (t_hrs_' t)) lp
         (list_insert_ordered_abs p
           (raw_key_at (hrs_mem (t_hrs_' s)) p) xs) \<and>
       raw_sentinel_max (hrs_mem (t_hrs_' t)) lp
     \<rbrace>"
proof -
  let ?h = "hrs_mem (t_hrs_' s)"
  note heap_effect = raw_vListInsert_ordered_empty_heap_effect[
    OF rel empty fresh sentinel]
  have transformer_effect:
    "raw_ordered_empty_effect ?h
       (raw_ordered_insert_empty_heap ?h lp p) lp p"
    by (rule raw_ordered_insert_empty_transformer_effect[
          OF rel empty fresh])
  have relation_post:
    "raw_xlist_rel (raw_ordered_insert_empty_heap ?h lp p) lp
       (list_insert_ordered_abs p (raw_key_at ?h p) xs)"
    by (rule raw_ordered_empty_effect_refines[
          OF rel empty fresh transformer_effect])
  have sentinel_frame:
    "raw_key_at (raw_ordered_insert_empty_heap ?h lp p)
       (raw_end_item lp) = raw_key_at ?h (raw_end_item lp)"
    using transformer_effect by (simp add: raw_ordered_empty_effect_def)
  have sentinel_post:
    "raw_sentinel_max (raw_ordered_insert_empty_heap ?h lp p) lp"
    using sentinel sentinel_frame by (simp add: raw_sentinel_max_def)
  show ?thesis
    apply (rule runs_to_weaken[OF heap_effect])
    using relation_post sentinel_post by auto
qed

corollary raw_vListInsert_ordered_empty_refines_ordered:
  assumes ordered:
    "raw_ordered_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and empty: "ring xs = []"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "vListInsert' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       raw_ordered_xlist_rel (hrs_mem (t_hrs_' t)) lp
         (list_insert_ordered_abs p
           (raw_key_at (hrs_mem (t_hrs_' s)) p) xs)
     \<rbrace>"
proof -
  let ?h = "hrs_mem (t_hrs_' s)"
  have rel: "raw_xlist_rel ?h lp xs"
    using ordered by (simp add: raw_ordered_xlist_rel_def)
  have sentinel: "raw_sentinel_max ?h lp"
    using ordered by (simp add: raw_ordered_xlist_rel_def)
  note heap_effect = raw_vListInsert_ordered_empty_heap_effect[
    OF rel empty fresh sentinel]
  have relation_post:
    "raw_ordered_xlist_rel (raw_ordered_insert_empty_heap ?h lp p) lp
       (list_insert_ordered_abs p (raw_key_at ?h p) xs)"
    by (rule raw_ordered_insert_empty_transformer_refines_ordered[
          OF ordered empty fresh])
  show ?thesis
    apply (rule runs_to_weaken[OF heap_effect])
    using relation_post by auto
qed

theorem raw_vListInsert_ordered_empty_max_refines:
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
       raw_xlist_rel (hrs_mem (t_hrs_' t)) lp
         (list_insert_ordered_abs p (max_word :: 32 word) xs)
     \<rbrace>"
proof -
  let ?h = "hrs_mem (t_hrs_' s)"
  note heap_effect = raw_vListInsert_ordered_empty_max_heap_effect[
    OF rel empty fresh key_max]
  have transformer_effect:
    "raw_ordered_empty_effect ?h
       (raw_ordered_insert_empty_heap ?h lp p) lp p"
    by (rule raw_ordered_insert_empty_transformer_effect[
          OF rel empty fresh])
  have relation_post:
    "raw_xlist_rel (raw_ordered_insert_empty_heap ?h lp p) lp
       (list_insert_ordered_abs p (raw_key_at ?h p) xs)"
    by (rule raw_ordered_empty_effect_refines[
          OF rel empty fresh transformer_effect])
  show ?thesis
    apply (rule runs_to_weaken[OF heap_effect])
    using relation_post key_max by auto
qed

end
