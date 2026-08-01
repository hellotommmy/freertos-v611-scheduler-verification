theory List_V611_Raw_R6_Unlink_Locality
  imports "EAL6_FreeRTOS_V611_List_Raw_R6_Source_Guards.List_V611_Raw_R6_Source_Guards"
begin

text \<open>
  Field-precise unlink locality.  Removal writes successor.previous and
  predecessor.next.  These four-byte fields are treated as subregions of the
  real list or item object, so the proof remains valid when a neighbour is the
  embedded sentinel and does not require its fictitious eight-byte tail.
\<close>

definition raw_next_field_ptr ::
  "raw_node_id \<Rightarrow> raw_node_id ptr"
where
  "raw_next_field_ptr u =
     PTR(xLIST_ITEM_C ptr) &(u\<rightarrow>[''pxNext_C''])"

definition raw_previous_field_ptr ::
  "raw_node_id \<Rightarrow> raw_node_id ptr"
where
  "raw_previous_field_ptr u =
     PTR(xLIST_ITEM_C ptr) &(u\<rightarrow>[''pxPrevious_C''])"

definition raw_pointer_field_region ::
  "raw_node_id ptr \<Rightarrow> addr set"
where
  "raw_pointer_field_region f =
     {ptr_val f..+size_of TYPE(raw_node_id)}"

lemma raw_next_field_region_subset_item:
  "raw_pointer_field_region (raw_next_field_ptr u) \<subseteq>
   raw_item_region u"
  unfolding raw_pointer_field_region_def raw_next_field_ptr_def
    raw_item_region_def
  apply (simp add: field_lvalue_def xLIST_ITEM_C_pxNext_C_fl)
  apply (rule intvl_sub_offset)
  by (simp add: size_of_def)

lemma raw_previous_field_region_subset_item:
  "raw_pointer_field_region (raw_previous_field_ptr u) \<subseteq>
   raw_item_region u"
  unfolding raw_pointer_field_region_def raw_previous_field_ptr_def
    raw_item_region_def
  apply (simp add: field_lvalue_def xLIST_ITEM_C_pxPrevious_C_fl)
  apply (rule intvl_sub_offset)
  by (simp add: size_of_def)

lemma raw_end_next_field_region_subset_list:
  "raw_pointer_field_region
      (raw_next_field_ptr (raw_end_item lp)) \<subseteq>
   raw_list_region lp"
  unfolding raw_pointer_field_region_def raw_next_field_ptr_def
    raw_list_region_def raw_end_item_def raw_sentinel_ptr_def
  apply (simp add: field_lvalue_def xLIST_ITEM_C_pxNext_C_fl
      xLIST_C_xListEnd_C_fl)
  apply (subst add.commute)
  apply (rule intvl_sub_offset)
  by (simp add: size_of_def)

lemma raw_end_previous_field_region_subset_list:
  "raw_pointer_field_region
      (raw_previous_field_ptr (raw_end_item lp)) \<subseteq>
   raw_list_region lp"
  unfolding raw_pointer_field_region_def raw_previous_field_ptr_def
    raw_list_region_def raw_end_item_def raw_sentinel_ptr_def
  apply (simp add: field_lvalue_def xLIST_ITEM_C_pxPrevious_C_fl
      xLIST_C_xListEnd_C_fl)
  apply (subst add.commute)
  apply (rule intvl_sub_offset)
  by (simp add: size_of_def)

lemma raw_pointer_field_update_preserves_disjoint_item:
  assumes disjoint:
    "raw_pointer_field_region f \<inter> raw_item_region p = {}"
  shows
    "h_val (heap_update f (q :: raw_node_id) h) p = h_val h p"
proof -
  have byte_disjoint:
    "{ptr_val f..+
       length (to_bytes q
         (heap_list h (size_of TYPE(raw_node_id)) (ptr_val f)))} \<inter>
     {ptr_val p..+size_of TYPE(xLIST_ITEM_C)} = {}"
    using disjoint
    by (simp add: raw_pointer_field_region_def raw_item_region_def)
  have heap_lists_same:
    "heap_list
       (heap_update_list (ptr_val f)
         (to_bytes q
           (heap_list h (size_of TYPE(raw_node_id)) (ptr_val f))) h)
       (size_of TYPE(xLIST_ITEM_C)) (ptr_val p) =
     heap_list h (size_of TYPE(xLIST_ITEM_C)) (ptr_val p)"
    by (rule heap_list_update_disjoint_same[OF byte_disjoint])
  show ?thesis
    unfolding h_val_def heap_update_def
    using heap_lists_same by simp
qed

lemma raw_cycle_next_field_disjoint_from_other_item:
  assumes layout: "raw_xlist_layout lp rs"
    and p_member: "p \<in> set rs"
    and u_member: "u \<in> insert (raw_end_item lp) (set rs)"
    and different: "u \<noteq> p"
  shows
    "raw_pointer_field_region (raw_next_field_ptr u) \<inter>
     raw_item_region p = {}"
proof (cases "u = raw_end_item lp")
  case True
  have p_list:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using layout p_member
    by (auto simp: raw_xlist_layout_def)
  show ?thesis
    using raw_end_next_field_region_subset_list[where lp=lp] p_list True
    by blast
next
  case False
  have u_real: "u \<in> set rs" using u_member False by simp
  have p_u:
    "raw_item_region p \<inter> raw_item_region u = {}"
    using layout p_member u_real different
    by (auto simp: raw_xlist_layout_def)
  show ?thesis
    using raw_next_field_region_subset_item[where u=u] p_u by blast
qed

lemma raw_cycle_previous_field_disjoint_from_other_item:
  assumes layout: "raw_xlist_layout lp rs"
    and p_member: "p \<in> set rs"
    and u_member: "u \<in> insert (raw_end_item lp) (set rs)"
    and different: "u \<noteq> p"
  shows
    "raw_pointer_field_region (raw_previous_field_ptr u) \<inter>
     raw_item_region p = {}"
proof (cases "u = raw_end_item lp")
  case True
  have p_list:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using layout p_member
    by (auto simp: raw_xlist_layout_def)
  show ?thesis
    using raw_end_previous_field_region_subset_list[where lp=lp] p_list True
    by blast
next
  case False
  have u_real: "u \<in> set rs" using u_member False by simp
  have p_u:
    "raw_item_region p \<inter> raw_item_region u = {}"
    using layout p_member u_real different
    by (auto simp: raw_xlist_layout_def)
  show ?thesis
    using raw_previous_field_region_subset_item[where u=u] p_u by blast
qed

lemma raw_xlist_rel_member_neighbours_not_self:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_next_at h lp p \<noteq> p \<and>
     raw_prev_at h lp p \<noteq> p"
proof -
  let ?e = "raw_end_item lp"
  obtain before after where split: "ring xs = before @ p # after"
    and p_fresh: "p \<notin> set before"
    using split_list_first[OF member] by blast
  have distinct_cycle: "distinct (?e # ring xs)"
    using raw_xlist_rel_distinct_cycle_nodes[OF rel] by simp
  have split_distinct: "distinct (?e # (before @ p # after))"
    using distinct_cycle split by simp
  have old_path:
    "list_all
      (\<lambda>(u, v). raw_next_at h lp u = v \<and> raw_prev_at h lp v = u)
      (raw_path_edges ?e (before @ p # after) ?e)"
    using rel split
    by (simp add: raw_xlist_rel_def raw_xlist_view_def
        raw_ring_links_path_iff)
  have entry:
    "(last (?e # before), p) \<in>
      set (raw_path_edges ?e (before @ p # after) ?e)"
    by (rule raw_path_edges_entry)
  have exit:
    "(p, hd (after @ [?e])) \<in>
      set (raw_path_edges ?e (before @ p # after) ?e)"
    by (rule raw_path_edges_exit)
  have previous:
    "raw_prev_at h lp p = last (?e # before)"
    using old_path entry by (auto simp: list_all_iff)
  have next_eq:
    "raw_next_at h lp p = hd (after @ [?e])"
    using old_path exit by (auto simp: list_all_iff)
  have p_not_before: "p \<notin> set (?e # before)"
    using split_distinct by auto
  have previous_member: "last (?e # before) \<in> set (?e # before)"
    by simp
  have previous_ne: "last (?e # before) \<noteq> p"
    using p_not_before previous_member by blast
  have p_not_after: "p \<notin> set (after @ [?e])"
    using split_distinct by auto
  have next_member: "hd (after @ [?e]) \<in> set (after @ [?e])"
    by (rule hd_in_set) simp
  have next_ne: "hd (after @ [?e]) \<noteq> p"
    using p_not_after next_member by blast
  show ?thesis using next_eq previous next_ne previous_ne by simp
qed

lemma raw_remove_successor_previous_field_disjoint:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_pointer_field_region
       (raw_previous_field_ptr
         (xLIST_ITEM_C.pxNext_C (h_val h p))) \<inter>
     raw_item_region p = {}"
proof -
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have links: "raw_ring_links h lp (ring xs)"
    using rel
    by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have cycle_member:
    "p \<in> insert (raw_end_item lp) (set (ring xs))"
    using member by simp
  have successor_member:
    "raw_next_at h lp p \<in>
       insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_ring_links_next_closed[OF links cycle_member])
  have successor_ne: "raw_next_at h lp p \<noteq> p"
    using raw_xlist_rel_member_neighbours_not_self[OF rel member]
    by blast
  have field_disjoint:
    "raw_pointer_field_region
       (raw_previous_field_ptr (raw_next_at h lp p)) \<inter>
     raw_item_region p = {}"
    by (rule raw_cycle_previous_field_disjoint_from_other_item[
          OF layout member successor_member successor_ne])
  show ?thesis
    using field_disjoint raw_full_next_is_sentinel_safe[
      where h=h and u=p and lp=lp]
    by simp
qed

lemma raw_remove_predecessor_next_field_disjoint:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_pointer_field_region
       (raw_next_field_ptr
         (xLIST_ITEM_C.pxPrevious_C (h_val h p))) \<inter>
     raw_item_region p = {}"
proof -
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have links: "raw_ring_links h lp (ring xs)"
    using rel
    by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have cycle_member:
    "p \<in> insert (raw_end_item lp) (set (ring xs))"
    using member by simp
  have predecessor_member:
    "raw_prev_at h lp p \<in>
       insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_ring_links_prev_closed[OF links cycle_member])
  have predecessor_ne: "raw_prev_at h lp p \<noteq> p"
    using raw_xlist_rel_member_neighbours_not_self[OF rel member]
    by blast
  have field_disjoint:
    "raw_pointer_field_region
       (raw_next_field_ptr (raw_prev_at h lp p)) \<inter>
     raw_item_region p = {}"
    by (rule raw_cycle_next_field_disjoint_from_other_item[
          OF layout member predecessor_member predecessor_ne])
  show ?thesis
    using field_disjoint raw_full_previous_is_sentinel_safe[
      where h=h and u=p and lp=lp]
    by simp
qed

lemma raw_remove_first_unlink_preserves_item:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "h_val
       (heap_update
         (raw_previous_field_ptr
           (xLIST_ITEM_C.pxNext_C (h_val h p)))
         (xLIST_ITEM_C.pxPrevious_C (h_val h p)) h)
       p =
     h_val h p"
  apply (rule raw_pointer_field_update_preserves_disjoint_item)
  by (rule raw_remove_successor_previous_field_disjoint[OF rel member])

lemma raw_remove_two_unlink_writes_preserve_item:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  defines
    "h1 \<equiv>
       heap_update
         (raw_previous_field_ptr
           (xLIST_ITEM_C.pxNext_C (h_val h p)))
         (xLIST_ITEM_C.pxPrevious_C (h_val h p)) h"
  shows
    "h_val
       (heap_update
         (raw_next_field_ptr
           (xLIST_ITEM_C.pxPrevious_C (h_val h1 p)))
         (xLIST_ITEM_C.pxNext_C (h_val h1 p)) h1)
       p =
     h_val h p"
proof -
  have first_same: "h_val h1 p = h_val h p"
    unfolding h1_def
    by (rule raw_remove_first_unlink_preserves_item[OF rel member])
  have second_disjoint:
    "raw_pointer_field_region
       (raw_next_field_ptr
         (xLIST_ITEM_C.pxPrevious_C (h_val h1 p))) \<inter>
     raw_item_region p = {}"
    using raw_remove_predecessor_next_field_disjoint[OF rel member]
      first_same
    by simp
  have second_same:
    "h_val
       (heap_update
         (raw_next_field_ptr
           (xLIST_ITEM_C.pxPrevious_C (h_val h1 p)))
         (xLIST_ITEM_C.pxNext_C (h_val h1 p)) h1)
       p =
     h_val h1 p"
    by (rule raw_pointer_field_update_preserves_disjoint_item[
          OF second_disjoint])
  show ?thesis using second_same first_same by simp
qed

lemma raw_general_remove_previous_guard_after_first_unlink:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "c_guard
      (xLIST_ITEM_C.pxPrevious_C
        (h_val
          (heap_update
            (PTR(xLIST_ITEM_C ptr)
              &(xLIST_ITEM_C.pxNext_C
                 (h_val (hrs_mem (t_hrs_' s)) p)
                   \<rightarrow>[''pxPrevious_C'']))
            (xLIST_ITEM_C.pxPrevious_C
              (h_val (hrs_mem (t_hrs_' s)) p))
            (hrs_mem (t_hrs_' s)))
          p))"
proof -
  let ?h = "hrs_mem (t_hrs_' s)"
  have stable:
    "h_val
       (heap_update
         (raw_previous_field_ptr
           (xLIST_ITEM_C.pxNext_C (h_val ?h p)))
         (xLIST_ITEM_C.pxPrevious_C (h_val ?h p)) ?h)
       p =
     h_val ?h p"
    by (rule raw_remove_first_unlink_preserves_item[OF rel member])
  have initial:
    "c_guard (xLIST_ITEM_C.pxPrevious_C (h_val ?h p))"
    by (rule raw_general_remove_previous_guard[OF rel member])
  show ?thesis
    using stable initial
    by (simp add: raw_previous_field_ptr_def)
qed

lemma raw_general_remove_container_guard_after_two_unlinks:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "let h0 = hrs_mem (t_hrs_' s)
     in let h1 = heap_update
           (PTR(xLIST_ITEM_C ptr)
             &(xLIST_ITEM_C.pxNext_C (h_val h0 p)
                 \<rightarrow>[''pxPrevious_C'']))
           (xLIST_ITEM_C.pxPrevious_C (h_val h0 p)) h0
     in let h2 = heap_update
           (PTR(xLIST_ITEM_C ptr)
             &(xLIST_ITEM_C.pxPrevious_C (h_val h1 p)
                 \<rightarrow>[''pxNext_C'']))
           (xLIST_ITEM_C.pxNext_C (h_val h1 p)) h1
     in c_guard
       (PTR_COERCE(unit \<rightarrow> xLIST_C)
         (pvContainer_C (h_val h2 p)))"
proof -
  let ?h0 = "hrs_mem (t_hrs_' s)"
  let ?h1 =
    "heap_update
      (raw_previous_field_ptr
        (xLIST_ITEM_C.pxNext_C (h_val ?h0 p)))
      (xLIST_ITEM_C.pxPrevious_C (h_val ?h0 p)) ?h0"
  let ?h2 =
    "heap_update
      (raw_next_field_ptr
        (xLIST_ITEM_C.pxPrevious_C (h_val ?h1 p)))
      (xLIST_ITEM_C.pxNext_C (h_val ?h1 p)) ?h1"
  have stable: "h_val ?h2 p = h_val ?h0 p"
    by (rule raw_remove_two_unlink_writes_preserve_item[OF rel member])
  have initial:
    "c_guard
      (PTR_COERCE(unit \<rightarrow> xLIST_C)
        (pvContainer_C (h_val ?h0 p)))"
    by (rule raw_general_remove_container_list_guard[OF rel member])
  show ?thesis
    using stable initial
    by (simp add: raw_previous_field_ptr_def raw_next_field_ptr_def)
qed

lemma raw_general_remove_container_guard_after_two_unlinks_exact:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "c_guard
      (PTR_COERCE(unit \<rightarrow> xLIST_C)
        (pvContainer_C
          (h_val
            (heap_update
              (PTR(xLIST_ITEM_C ptr)
                &(xLIST_ITEM_C.pxPrevious_C
                   (h_val
                     (heap_update
                       (PTR(xLIST_ITEM_C ptr)
                         &(xLIST_ITEM_C.pxNext_C
                            (h_val (hrs_mem (t_hrs_' s)) p)
                              \<rightarrow>[''pxPrevious_C'']))
                       (xLIST_ITEM_C.pxPrevious_C
                         (h_val (hrs_mem (t_hrs_' s)) p))
                       (hrs_mem (t_hrs_' s)))
                     p)\<rightarrow>[''pxNext_C'']))
              (xLIST_ITEM_C.pxNext_C
                (h_val
                  (heap_update
                    (PTR(xLIST_ITEM_C ptr)
                      &(xLIST_ITEM_C.pxNext_C
                         (h_val (hrs_mem (t_hrs_' s)) p)
                           \<rightarrow>[''pxPrevious_C'']))
                    (xLIST_ITEM_C.pxPrevious_C
                      (h_val (hrs_mem (t_hrs_' s)) p))
                    (hrs_mem (t_hrs_' s)))
                  p))
              (heap_update
                (PTR(xLIST_ITEM_C ptr)
                  &(xLIST_ITEM_C.pxNext_C
                     (h_val (hrs_mem (t_hrs_' s)) p)
                       \<rightarrow>[''pxPrevious_C'']))
                (xLIST_ITEM_C.pxPrevious_C
                  (h_val (hrs_mem (t_hrs_' s)) p))
                (hrs_mem (t_hrs_' s))))
            p)))"
proof -
  let ?h0 = "hrs_mem (t_hrs_' s)"
  let ?h1 =
    "heap_update
      (raw_previous_field_ptr
        (xLIST_ITEM_C.pxNext_C (h_val ?h0 p)))
      (xLIST_ITEM_C.pxPrevious_C (h_val ?h0 p)) ?h0"
  let ?h2 =
    "heap_update
      (raw_next_field_ptr
        (xLIST_ITEM_C.pxPrevious_C (h_val ?h1 p)))
      (xLIST_ITEM_C.pxNext_C (h_val ?h1 p)) ?h1"
  have stable: "h_val ?h2 p = h_val ?h0 p"
    by (rule raw_remove_two_unlink_writes_preserve_item[OF rel member])
  have initial:
    "c_guard
      (PTR_COERCE(unit \<rightarrow> xLIST_C)
        (pvContainer_C (h_val ?h0 p)))"
    by (rule raw_general_remove_container_list_guard[OF rel member])
  show ?thesis
    using stable initial
    by (simp add: raw_previous_field_ptr_def raw_next_field_ptr_def)
qed

theorem raw_vListRemove_general_result:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r t. r = Result ()\<rbrace>"
  unfolding vListRemove'_def
  apply runs_to_vcg
  apply (simp_all only: hrs_mem_update)
  apply ((rule
      raw_general_remove_previous_guard_after_first_unlink[OF rel member]
    | rule raw_general_remove_container_guard_after_two_unlinks_exact[
        OF rel member]
    | rule raw_general_remove_item_guard[OF rel member]
    | rule raw_general_remove_next_guard[OF rel member]
    | rule raw_general_remove_previous_guard[OF rel member]
    | rule raw_general_remove_container_list_guard[OF rel member])+)
  done

end
