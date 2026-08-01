theory List_V611_Raw_R6_Source_Guards
  imports "EAL6_FreeRTOS_V611_List_Raw_R6_Splice.List_V611_Raw_R6_Splice"
begin

text \<open>
  General-N source-execution entrance.  Fresh-item writes are shown local at
  the byte heap before opening vListInsertEnd'.  Sentinel observations are
  routed through the real mini-item prefix; no full sentinel allocation is
  introduced.
\<close>

lemma raw_item_update_preserves_disjoint_list:
  assumes disjoint:
    "raw_item_region p \<inter> raw_list_region lp = {}"
  shows
    "h_val (heap_update p (v :: xLIST_ITEM_C) h) lp = h_val h lp"
proof -
  have byte_disjoint:
    "{ptr_val p..+
       length (to_bytes v
         (heap_list h (size_of TYPE(xLIST_ITEM_C)) (ptr_val p)))} \<inter>
     {ptr_val lp..+size_of TYPE(xLIST_C)} = {}"
    using disjoint
    by (simp add: raw_item_region_def raw_list_region_def)
  have heap_lists_same:
    "heap_list
       (heap_update_list (ptr_val p)
         (to_bytes v
           (heap_list h (size_of TYPE(xLIST_ITEM_C)) (ptr_val p))) h)
       (size_of TYPE(xLIST_C)) (ptr_val lp) =
     heap_list h (size_of TYPE(xLIST_C)) (ptr_val lp)"
    by (rule heap_list_update_disjoint_same[OF byte_disjoint])
  show ?thesis
    unfolding h_val_def heap_update_def
    using heap_lists_same by simp
qed

lemma raw_item_update_preserves_disjoint_item:
  assumes disjoint:
    "raw_item_region p \<inter> raw_item_region q = {}"
  shows
    "h_val (heap_update p (v :: xLIST_ITEM_C) h) q = h_val h q"
proof -
  have byte_disjoint:
    "{ptr_val p..+
       length (to_bytes v
         (heap_list h (size_of TYPE(xLIST_ITEM_C)) (ptr_val p)))} \<inter>
     {ptr_val q..+size_of TYPE(xLIST_ITEM_C)} = {}"
    using disjoint by (simp add: raw_item_region_def)
  have heap_lists_same:
    "heap_list
       (heap_update_list (ptr_val p)
         (to_bytes v
           (heap_list h (size_of TYPE(xLIST_ITEM_C)) (ptr_val p))) h)
       (size_of TYPE(xLIST_ITEM_C)) (ptr_val q) =
     heap_list h (size_of TYPE(xLIST_ITEM_C)) (ptr_val q)"
    by (rule heap_list_update_disjoint_same[OF byte_disjoint])
  show ?thesis
    unfolding h_val_def heap_update_def
    using heap_lists_same by simp
qed

lemma raw_fresh_item_update_preserves_cycle_next:
  assumes layout: "raw_xlist_layout lp rs"
    and fresh: "raw_fresh_for_insert lp rs p"
    and member: "u \<in> insert (raw_end_item lp) (set rs)"
  shows
    "xLIST_ITEM_C.pxNext_C
       (h_val (heap_update p (v :: xLIST_ITEM_C) h) u) =
     xLIST_ITEM_C.pxNext_C (h_val h u)"
proof (cases "u = raw_end_item lp")
  case True
  have disjoint:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have list_same:
    "h_val (heap_update p v h) lp = h_val h lp"
    by (rule raw_item_update_preserves_disjoint_list[OF disjoint])
  show ?thesis
    using True list_same
      raw_sentinel_next_prefix_generic[
        where h="heap_update p v h" and lp=lp]
      raw_sentinel_next_prefix_generic[where h=h and lp=lp]
    by (simp add: raw_end_item_def)
next
  case False
  have u_member: "u \<in> set rs"
    using member False by simp
  have disjoint:
    "raw_item_region p \<inter> raw_item_region u = {}"
    using fresh u_member
    by (simp add: raw_fresh_for_insert_def)
  have item_same: "h_val (heap_update p v h) u = h_val h u"
    by (rule raw_item_update_preserves_disjoint_item[OF disjoint])
  show ?thesis using item_same by simp
qed

lemma raw_fresh_two_item_updates_preserve_cycle_next:
  assumes layout: "raw_xlist_layout lp rs"
    and fresh: "raw_fresh_for_insert lp rs p"
    and member: "u \<in> insert (raw_end_item lp) (set rs)"
  shows
    "xLIST_ITEM_C.pxNext_C
       (h_val
         (heap_update p (v2 :: xLIST_ITEM_C)
           (heap_update p (v1 :: xLIST_ITEM_C) h)) u) =
     xLIST_ITEM_C.pxNext_C (h_val h u)"
proof -
  have first:
    "xLIST_ITEM_C.pxNext_C (h_val (heap_update p v1 h) u) =
     xLIST_ITEM_C.pxNext_C (h_val h u)"
    by (rule raw_fresh_item_update_preserves_cycle_next[OF
          layout fresh member])
  have second:
    "xLIST_ITEM_C.pxNext_C
       (h_val (heap_update p v2 (heap_update p v1 h)) u) =
     xLIST_ITEM_C.pxNext_C (h_val (heap_update p v1 h) u)"
    by (rule raw_fresh_item_update_preserves_cycle_next[OF
          layout fresh member])
  show ?thesis using first second by simp
qed

lemma raw_general_insert_index_guard:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "c_guard
      (pxIndex_C
        (h_val (hrs_mem (t_hrs_' s)) lp))"
  using raw_vListInsertEnd_dynamic_guards[OF rel fresh] by blast

lemma raw_general_insert_list_guard:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows "c_guard lp"
  using raw_vListInsertEnd_dynamic_guards[OF rel fresh] by blast

lemma raw_general_insert_item_guard:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows "c_guard p"
  using raw_vListInsertEnd_dynamic_guards[OF rel fresh] by blast

lemma raw_general_insert_index_next_guard_after_item_updates:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "c_guard
      (xLIST_ITEM_C.pxNext_C
        (h_val
          (heap_update p (v2 :: xLIST_ITEM_C)
            (heap_update p (v1 :: xLIST_ITEM_C)
              (hrs_mem (t_hrs_' s))))
          (pxIndex_C
            (h_val (hrs_mem (t_hrs_' s)) lp))))"
proof -
  let ?h = "hrs_mem (t_hrs_' s)"
  let ?i = "pxIndex_C (h_val ?h lp)"
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have member:
    "?i \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_xlist_rel_index_in_cycle[OF rel])
  have stable:
    "xLIST_ITEM_C.pxNext_C
       (h_val (heap_update p v2 (heap_update p v1 ?h)) ?i) =
     xLIST_ITEM_C.pxNext_C (h_val ?h ?i)"
    by (rule raw_fresh_two_item_updates_preserve_cycle_next[OF
          layout fresh member])
  have initial_guard:
    "c_guard (xLIST_ITEM_C.pxNext_C (h_val ?h ?i))"
    using raw_vListInsertEnd_dynamic_guards[OF rel fresh] by blast
  show ?thesis using stable initial_guard by simp
qed

theorem raw_vListInsertEnd_general_result:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "vListInsertEnd' lp p \<bullet> s
     \<lbrace>\<lambda>r t. r = Result ()\<rbrace>"
  unfolding vListInsertEnd'_def
  apply runs_to_vcg
  apply (simp_all only: hrs_mem_update)
  apply ((rule
      raw_general_insert_index_next_guard_after_item_updates[OF rel fresh]
    | rule raw_general_insert_index_guard[OF rel fresh]
    | rule raw_general_insert_list_guard[OF rel fresh]
    | rule raw_general_insert_item_guard[OF rel fresh])+)
  done

lemma raw_general_remove_item_guard:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows "c_guard p"
  using raw_vListRemove_dynamic_guards[OF rel member] by blast

lemma raw_general_remove_next_guard:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "c_guard
      (xLIST_ITEM_C.pxNext_C
        (h_val (hrs_mem (t_hrs_' s)) p))"
  using raw_vListRemove_dynamic_guards[OF rel member] by blast

lemma raw_general_remove_previous_guard:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "c_guard
      (xLIST_ITEM_C.pxPrevious_C
        (h_val (hrs_mem (t_hrs_' s)) p))"
  using raw_vListRemove_dynamic_guards[OF rel member] by blast

lemma raw_general_remove_container_list_guard:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "c_guard
      (PTR_COERCE(unit \<rightarrow> xLIST_C)
        (pvContainer_C (h_val (hrs_mem (t_hrs_' s)) p)))"
  using raw_vListRemove_dynamic_guards[OF rel member] by blast

end
