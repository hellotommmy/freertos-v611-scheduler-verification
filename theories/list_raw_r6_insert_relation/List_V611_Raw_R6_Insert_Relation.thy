theory List_V611_Raw_R6_Insert_Relation
  imports "EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Relation.List_V611_Raw_R6_Remove_Relation"
begin

text \<open>
  Pure representation assembler for general-N insertion.  The generated C
  body is kept out of this theory; its later effect theorem must supply the
  listed count, cursor, topology, and payload observations.
\<close>

lemma length_insert_after:
  assumes member: "c \<in> set rs"
  shows "length (insert_after c p rs) = Suc (length rs)"
  using member
  by (induction rs) auto

lemma list_insert_end_ring_set:
  assumes wf: "xlist_wf xs"
  shows
    "set (ring (list_insert_end_abs p k xs)) =
     insert p (set (ring xs))"
proof (cases "cursor xs")
  case None
  then show ?thesis by (simp add: list_insert_end_abs_def)
next
  case (Some c)
  have member: "c \<in> set (ring xs)"
    using wf Some by (auto simp: xlist_wf_def)
  show ?thesis
    using Some set_insert_after[OF member]
    by (simp add: list_insert_end_abs_def)
qed

lemma list_insert_end_ring_length:
  assumes wf: "xlist_wf xs"
  shows
    "length (ring (list_insert_end_abs p k xs)) =
     Suc (length (ring xs))"
proof (cases "cursor xs")
  case None
  then show ?thesis by (simp add: list_insert_end_abs_def)
next
  case (Some c)
  have member: "c \<in> set (ring xs)"
    using wf Some by (auto simp: xlist_wf_def)
  show ?thesis
    using Some length_insert_after[OF member, where p=p]
    by (simp add: list_insert_end_abs_def)
qed

lemma raw_xlist_rel_index_eq_cursor_node:
  assumes rel: "raw_xlist_rel h lp xs"
  shows
    "pxIndex_C (h_val h lp) = raw_cursor_node lp xs"
proof -
  have cursor_eq: "cursor xs = raw_cursor_at h lp"
    by (rule raw_xlist_rel_cursorD[OF rel])
  show ?thesis
  proof (cases "pxIndex_C (h_val h lp) = raw_end_item lp")
    case True
    have cursor_none: "cursor xs = None"
      using cursor_eq True by (simp add: raw_cursor_at_def)
    show ?thesis
      using True cursor_none by (simp add: raw_cursor_node_def)
  next
    case False
    have cursor_some:
      "cursor xs = Some (pxIndex_C (h_val h lp))"
      using cursor_eq False by (simp add: raw_cursor_at_def)
    show ?thesis
      using cursor_some by (simp add: raw_cursor_node_def)
  qed
qed

lemma raw_xlist_rel_insert_endI:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and count:
      "unat (uxNumberOfItems_C (h_val h' lp)) =
       length (ring (list_insert_end_abs p k xs))"
    and cursor:
      "raw_cursor_at h' lp = cursor (list_insert_end_abs p k xs)"
    and links:
      "raw_ring_links h' lp (ring (list_insert_end_abs p k xs))"
    and new_key: "raw_key_at h' p = k"
    and new_container:
      "pvContainer_C (h_val h' p) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    and old_frame:
      "\<And>q. q \<in> set (ring xs) \<Longrightarrow>
        raw_key_at h' q = raw_key_at h q \<and>
        pvContainer_C (h_val h' q) = pvContainer_C (h_val h q)"
  shows
    "raw_xlist_rel h' lp (list_insert_end_abs p k xs)"
proof -
  let ?ys = "list_insert_end_abs p k xs"
  have old_wf: "xlist_wf xs"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have p_fresh: "p \<notin> set (ring xs)"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have new_wf: "xlist_wf ?ys"
    by (rule list_insert_end_preserves_wf[OF old_wf p_fresh])
  have set_eq: "set (ring ?ys) = insert p (set (ring xs))"
    by (rule list_insert_end_ring_set[OF old_wf])
  have old_layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have new_layout: "raw_xlist_layout lp (ring ?ys)"
    by (rule raw_xlist_layout_extend_set[OF old_layout fresh set_eq])
  have live:
    "\<forall>q \<in> set (ring ?ys).
       item_key ?ys q = raw_key_at h' q \<and>
       pvContainer_C (h_val h' q) =
         PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
  proof (intro ballI)
    fix q
    assume q_new: "q \<in> set (ring ?ys)"
    have cases: "q = p \<or> q \<in> set (ring xs)"
      using q_new set_eq by simp
    from cases show
      "item_key ?ys q = raw_key_at h' q \<and>
       pvContainer_C (h_val h' q) =
         PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    proof
      assume q_eq: "q = p"
      then show ?thesis
        using new_key new_container
        by (simp add: list_insert_end_abs_def)
    next
      assume q_old: "q \<in> set (ring xs)"
      have q_ne: "q \<noteq> p" using p_fresh q_old by auto
      have old_live:
        "item_key xs q = raw_key_at h q \<and>
         pvContainer_C (h_val h q) =
           PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
        by (rule raw_xlist_rel_live_itemD[OF rel q_old])
      have frame:
        "raw_key_at h' q = raw_key_at h q \<and>
         pvContainer_C (h_val h' q) = pvContainer_C (h_val h q)"
        by (rule old_frame[OF q_old])
      show ?thesis
        using q_ne old_live frame
        by (simp add: list_insert_end_abs_def)
    qed
  qed
  show ?thesis
    unfolding raw_xlist_rel_def
  proof (intro conjI)
    show "raw_xlist_layout lp (ring ?ys)" by (rule new_layout)
    show "raw_xlist_view h' lp ?ys"
      unfolding raw_xlist_view_def
    proof (intro conjI)
      show "xlist_wf ?ys" by (rule new_wf)
      show
        "unat (uxNumberOfItems_C (h_val h' lp)) = length (ring ?ys)"
        by (rule count)
      show "cursor ?ys = raw_cursor_at h' lp"
        using cursor by simp
      show "raw_ring_links h' lp (ring ?ys)" by (rule links)
      show
        "\<forall>q \<in> set (ring ?ys).
          item_key ?ys q = raw_key_at h' q \<and>
          pvContainer_C (h_val h' q) =
            PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
        by (rule live)
    qed
  qed
qed

end
