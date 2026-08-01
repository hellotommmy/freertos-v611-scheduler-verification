theory List_V611_Raw_R6_Remove_Relation
  imports "EAL6_FreeRTOS_V611_List_Raw_R6_Unlink_Locality.List_V611_Raw_R6_Unlink_Locality"
begin

text \<open>
  Relation-level deletion transfer.  This checker brick deliberately knows
  nothing about the generated C body: a later source VCG only has to supply
  the count, cursor, topology, and live-item frame obligations listed here.
\<close>

lemma raw_xlist_remove_count_transfer:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "unat (uxNumberOfItems_C (h_val h lp) - 1) =
     length (remove1 p (ring xs))"
proof -
  let ?w = "uxNumberOfItems_C (h_val h lp)"
  have count_eq: "unat ?w = length (ring xs)"
    by (rule raw_xlist_rel_countD[OF rel])
  have length_pos: "0 < length (ring xs)"
    using member by auto
  have word_nonzero: "?w \<noteq> 0"
    using count_eq length_pos by auto
  have predecessor_count: "Suc (unat (?w - 1)) = unat ?w"
    by (rule Suc_unat_minus_one[OF word_nonzero])
  have removed_length:
    "length (remove1 p (ring xs)) = length (ring xs) - 1"
    using member by (simp add: length_remove1)
  show ?thesis
    using count_eq length_pos predecessor_count removed_length by arith
qed

lemma raw_xlist_rel_removeI:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
    and count:
      "unat (uxNumberOfItems_C (h_val h' lp)) =
       length (remove1 p (ring xs))"
    and cursor:
      "raw_cursor_at h' lp = cursor (list_remove_abs p xs)"
    and links:
      "raw_ring_links h' lp (remove1 p (ring xs))"
    and live_frame:
      "\<And>q. q \<in> set (remove1 p (ring xs)) \<Longrightarrow>
        raw_key_at h' q = raw_key_at h q \<and>
        pvContainer_C (h_val h' q) = pvContainer_C (h_val h q)"
  shows "raw_xlist_rel h' lp (list_remove_abs p xs)"
proof -
  let ?ys = "list_remove_abs p xs"
  have old_wf: "xlist_wf xs"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have new_wf: "xlist_wf ?ys"
    by (rule list_remove_preserves_wf[OF old_wf member])
  have old_layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have subset:
    "set (ring ?ys) \<subseteq> set (ring xs)"
    apply (simp add: list_remove_abs_def)
    by (rule set_remove1_subset)
  have new_layout: "raw_xlist_layout lp (ring ?ys)"
    by (rule raw_xlist_layout_subset[OF old_layout subset])
  have ring_eq: "ring ?ys = remove1 p (ring xs)"
    by (simp add: list_remove_abs_def)
  have live:
    "\<forall>q \<in> set (ring ?ys).
       item_key ?ys q = raw_key_at h' q \<and>
       pvContainer_C (h_val h' q) =
         PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
  proof (intro ballI)
    fix q
    assume q_new: "q \<in> set (ring ?ys)"
    have q_removed: "q \<in> set (remove1 p (ring xs))"
      using q_new ring_eq by simp
    have q_old: "q \<in> set (ring xs)"
      by (rule subsetD[OF set_remove1_subset q_removed])
    have old_live:
      "item_key xs q = raw_key_at h q \<and>
       pvContainer_C (h_val h q) =
         PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
      by (rule raw_xlist_rel_live_itemD[OF rel q_old])
    have frame:
      "raw_key_at h' q = raw_key_at h q \<and>
       pvContainer_C (h_val h' q) = pvContainer_C (h_val h q)"
      by (rule live_frame[OF q_removed])
    show
      "item_key ?ys q = raw_key_at h' q \<and>
       pvContainer_C (h_val h' q) =
         PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
      using old_live frame
      by (simp add: list_remove_abs_def)
  qed
  show ?thesis
    unfolding raw_xlist_rel_def
  proof (intro conjI)
    show "raw_xlist_layout lp (ring ?ys)"
      by (rule new_layout)
    show "raw_xlist_view h' lp ?ys"
      unfolding raw_xlist_view_def
    proof (intro conjI)
      show "xlist_wf ?ys" by (rule new_wf)
      show
        "unat (uxNumberOfItems_C (h_val h' lp)) = length (ring ?ys)"
        using count ring_eq by simp
      show "cursor ?ys = raw_cursor_at h' lp"
        using cursor by simp
      show "raw_ring_links h' lp (ring ?ys)"
        using links ring_eq by simp
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
