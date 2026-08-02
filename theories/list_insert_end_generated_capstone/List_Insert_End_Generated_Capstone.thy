theory List_Insert_End_Generated_Capstone
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Ordered_Insert_General_Refinement.Scheduler_Ordered_Insert_General_Refinement"
    "EAL6_FreeRTOS_V611_Scheduler_Universal_Capacity.Scheduler_Universal_Capacity"
begin

text \<open>
  Source-level Gate-L capstone for vListInsertEnd.  The arbitrary raw list,
  cursor, item key, insertion endpoints, source state, list address, and item
  address remain symbolic.  The exact footprint contains the four link fields,
  list index, new-item container, and list count written by the source.
\<close>

lemma raw_insert_end_index_heap_to_field:
  assumes guard: "c_guard lp"
  shows
    "raw_insert_index_heap h lp p =
     heap_update (raw_index_field_ptr lp) p h"
  unfolding raw_insert_index_heap_def raw_index_field_ptr_def
  apply (rule sym)
  by (rule xLIST_C_heap_update_fields(2)[OF guard])

lemma heap_update_raw_insert_end_index_external_frame:
  assumes outside: "a \<notin> raw_index_field_region lp"
  shows "heap_update (raw_index_field_ptr lp) v h a = h a"
  unfolding heap_update_def raw_index_field_region_def
  apply (rule heap_update_nmem_same)
  using outside by (simp add: raw_index_field_region_def)

definition raw_insert_end_exact_write_footprint ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow> raw_node_id \<Rightarrow> addr set"
where
  "raw_insert_end_exact_write_footprint h lp xs p =
     (let c = raw_cursor_node lp xs;
          q = raw_next_at h lp c
      in raw_pointer_field_region (raw_next_field_ptr p) \<union>
         raw_pointer_field_region (raw_previous_field_ptr p) \<union>
         raw_pointer_field_region (raw_previous_field_ptr q) \<union>
         raw_pointer_field_region (raw_next_field_ptr c) \<union>
         raw_index_field_region lp \<union>
         raw_container_field_region p \<union>
         raw_count_field_region lp)"

theorem raw_insert_concrete_heap_exact_external_frame:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and outside:
      "a \<notin> raw_insert_end_exact_write_footprint h lp xs p"
  shows "raw_insert_concrete_heap h lp xs p a = h a"
proof -
  let ?c = "raw_cursor_node lp xs"
  let ?q = "raw_next_at h lp ?c"
  let ?h1 = "raw_insert_next_heap h p ?q"
  let ?h2 = "raw_insert_previous_heap ?h1 p ?c"
  let ?h3 = "raw_insert_previous_heap ?h2 ?q p"
  let ?h4 = "raw_insert_next_heap ?h3 ?c p"
  let ?h5 = "raw_insert_index_heap ?h4 lp p"
  let ?h6 = "raw_insert_container_heap ?h5 lp p"
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have p_guard: "c_guard p"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have lp_guard: "c_guard lp"
    using layout by (simp add: raw_xlist_layout_def)
  have out_p_next:
    "a \<notin> raw_pointer_field_region (raw_next_field_ptr p)"
    using outside
    by (simp add: raw_insert_end_exact_write_footprint_def Let_def)
  have out_p_previous:
    "a \<notin> raw_pointer_field_region (raw_previous_field_ptr p)"
    using outside
    by (simp add: raw_insert_end_exact_write_footprint_def Let_def)
  have out_q_previous:
    "a \<notin> raw_pointer_field_region (raw_previous_field_ptr ?q)"
    using outside
    by (simp add: raw_insert_end_exact_write_footprint_def Let_def)
  have out_c_next:
    "a \<notin> raw_pointer_field_region (raw_next_field_ptr ?c)"
    using outside
    by (simp add: raw_insert_end_exact_write_footprint_def Let_def)
  have out_index: "a \<notin> raw_index_field_region lp"
    using outside
    by (simp add: raw_insert_end_exact_write_footprint_def Let_def)
  have out_container: "a \<notin> raw_container_field_region p"
    using outside
    by (simp add: raw_insert_end_exact_write_footprint_def Let_def)
  have out_count: "a \<notin> raw_count_field_region lp"
    using outside
    by (simp add: raw_insert_end_exact_write_footprint_def Let_def)
  have h1: "?h1 a = h a"
    unfolding raw_insert_next_heap_def
    by (rule heap_update_raw_pointer_field_external_frame[OF out_p_next])
  have h2: "?h2 a = ?h1 a"
    unfolding raw_insert_previous_heap_def
    by (rule heap_update_raw_pointer_field_external_frame[OF out_p_previous])
  have h3: "?h3 a = ?h2 a"
    unfolding raw_insert_previous_heap_def
    by (rule heap_update_raw_pointer_field_external_frame[OF out_q_previous])
  have h4: "?h4 a = ?h3 a"
    unfolding raw_insert_next_heap_def
    by (rule heap_update_raw_pointer_field_external_frame[OF out_c_next])
  have h5_field:
    "?h5 = heap_update (raw_index_field_ptr lp) p ?h4"
    by (rule raw_insert_end_index_heap_to_field[OF lp_guard])
  have h5: "?h5 a = ?h4 a"
    unfolding h5_field
    by (rule heap_update_raw_insert_end_index_external_frame[OF out_index])
  have h6_field:
    "?h6 = heap_update (raw_container_field_ptr p)
       (PTR_COERCE(xLIST_C \<rightarrow> unit) lp) ?h5"
    by (rule raw_insert_container_heap_to_field[OF p_guard])
  have h6: "?h6 a = ?h5 a"
    unfolding h6_field
    by (rule heap_update_raw_container_field_external_frame[OF out_container])
  have final_field:
    "raw_insert_count_heap ?h6 lp =
     heap_update (raw_count_field_ptr lp)
       (uxNumberOfItems_C (h_val ?h6 lp) + 1) ?h6"
    by (rule raw_insert_count_heap_to_field[OF lp_guard])
  have final: "raw_insert_count_heap ?h6 lp a = ?h6 a"
    unfolding final_field
    by (rule heap_update_raw_count_field_external_frame[OF out_count])
  show ?thesis
    using h1 h2 h3 h4 h5 h6 final
    by (simp add: raw_insert_concrete_heap_def Let_def)
qed

theorem raw_vListInsertEnd_general_source_capstone:
  assumes rel: "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "vListInsertEnd' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       raw_xlist_rel (hrs_mem (t_hrs_' t)) lp
         (list_insert_end_abs p
           (raw_key_at (hrs_mem (t_hrs_' s)) p) xs) \<and>
       (\<forall>a.
          a \<notin> raw_insert_end_exact_write_footprint
            (hrs_mem (t_hrs_' s)) lp xs p
          \<longrightarrow>
          hrs_mem (t_hrs_' t) a = hrs_mem (t_hrs_' s) a)
     \<rbrace>"
proof -
  let ?h = "hrs_mem (t_hrs_' s)"
  let ?h' = "raw_insert_concrete_heap ?h lp xs p"
  have capacity: "raw_count_can_increment xs"
    by (rule raw_xlist_rel_fresh_count_can_increment[OF rel fresh])
  note execution = raw_vListInsertEnd_general_heap_effect[OF rel fresh]
  have relation:
    "raw_xlist_rel ?h' lp
       (list_insert_end_abs p (raw_key_at ?h p) xs)"
    by (rule raw_insert_concrete_heap_refines[OF rel fresh capacity])
  have frame:
    "\<forall>a.
       a \<notin> raw_insert_end_exact_write_footprint ?h lp xs p
       \<longrightarrow> ?h' a = ?h a"
  proof (intro allI impI)
    fix a
    assume outside:
      "a \<notin> raw_insert_end_exact_write_footprint ?h lp xs p"
    show "?h' a = ?h a"
      by (rule raw_insert_concrete_heap_exact_external_frame[
            OF rel fresh outside])
  qed
  show ?thesis
    apply (rule runs_to_weaken[OF execution])
    using relation frame by auto
qed

text \<open>
  No premise above requires a non-empty ring or distinct insertion endpoints.
  Hence the empty-ring case, where cursor and successor are the same embedded
  sentinel, remains within the theorem.  This local capstone still does not
  establish scheduler-family or same-TCB Generic/Event frames.
\<close>

end
