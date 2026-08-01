theory Scheduler_P2_Insert_Frame
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Insert_Transform.Scheduler_P2_Insert_Transform"
begin

text \<open>
  Locality of the ordered-empty insertion transformer.  The generic lemma
  frames one disjoint third-party list root through all six source-ordered
  writes.  The P2 specialisations then carry the empty pending-ready root
  through ready-list removal, wake-key assignment, and delayed-list insertion.
\<close>

lemma raw_ordered_insert_empty_heap_preserves_disjoint_list:
  assumes roots:
      "raw_list_region lp \<inter> raw_list_region lq = {}"
    and item_target:
      "raw_item_region p \<inter> raw_list_region lq = {}"
  shows
    "h_val (raw_ordered_insert_empty_heap h lp p) lq = h_val h lq"
proof -
  let ?e = "raw_end_item lp"
  let ?h1 = "raw_insert_next_heap h p ?e"
  let ?h2 = "raw_insert_previous_heap ?h1 ?e p"
  let ?h3 = "raw_insert_previous_heap ?h2 p ?e"
  let ?h4 = "raw_insert_next_heap ?h3 ?e p"
  let ?h5 = "raw_insert_container_heap ?h4 lp p"

  have p_next_disjoint:
    "raw_pointer_field_region (raw_next_field_ptr p) \<inter>
       raw_list_region lq = {}"
    using raw_next_field_region_subset_item[where u=p] item_target
    by blast
  have p_previous_disjoint:
    "raw_pointer_field_region (raw_previous_field_ptr p) \<inter>
       raw_list_region lq = {}"
    using raw_previous_field_region_subset_item[where u=p] item_target
    by blast
  have end_next_disjoint:
    "raw_pointer_field_region (raw_next_field_ptr ?e) \<inter>
       raw_list_region lq = {}"
    using raw_end_next_field_region_subset_list[where lp=lp] roots
    by blast
  have end_previous_disjoint:
    "raw_pointer_field_region (raw_previous_field_ptr ?e) \<inter>
       raw_list_region lq = {}"
    using raw_end_previous_field_region_subset_list[where lp=lp] roots
    by blast

  have h1_frame: "h_val ?h1 lq = h_val h lq"
    unfolding raw_insert_next_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_list[
          OF p_next_disjoint])
  have h2_frame: "h_val ?h2 lq = h_val ?h1 lq"
    unfolding raw_insert_previous_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_list[
          OF end_previous_disjoint])
  have h3_frame: "h_val ?h3 lq = h_val ?h2 lq"
    unfolding raw_insert_previous_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_list[
          OF p_previous_disjoint])
  have h4_frame: "h_val ?h4 lq = h_val ?h3 lq"
    unfolding raw_insert_next_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_list[
          OF end_next_disjoint])
  have h5_frame: "h_val ?h5 lq = h_val ?h4 lq"
    unfolding raw_insert_container_heap_def
    by (rule raw_item_update_preserves_disjoint_list[OF item_target])
  have h6_frame:
    "h_val (raw_insert_count_heap ?h5 lp) lq = h_val ?h5 lq"
    unfolding raw_insert_count_heap_def
    by (rule raw_list_update_preserves_disjoint_list[OF roots])

  have
    "h_val (raw_ordered_insert_empty_heap h lp p) lq =
     h_val (raw_insert_count_heap ?h5 lp) lq"
    by (simp only: raw_ordered_insert_empty_heap_def Let_def)
  also have "... = h_val ?h5 lq" by (rule h6_frame)
  also have "... = h_val ?h4 lq" by (rule h5_frame)
  also have "... = h_val ?h3 lq" by (rule h4_frame)
  also have "... = h_val ?h2 lq" by (rule h3_frame)
  also have "... = h_val ?h1 lq" by (rule h2_frame)
  also have "... = h_val h lq" by (rule h1_frame)
  finally show ?thesis .
qed

lemma p2_remove_then_wake_pending_frame:
  fixes s :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R s p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))"
  shows
    "h_val
       (p2_remove_then_wake_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)) D)
       (abi_list_ptr (sr_pending R)) =
     h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
       (abi_list_ptr (sr_pending R))"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)"
  let ?ready = "abi_list_ptr (sr_ready R 2)"
  let ?pending = "abi_list_ptr (sr_pending R)"
  let ?p = "abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)"
  let ?hr = "raw_remove_concrete_heap ?h ?p"
  from p2_pre_ready2_raw_singletonE[OF decode lists]
  obtain ready_xs where
      ready_rel: "raw_xlist_rel ?h ?ready ready_xs"
    and ready_ring: "ring ready_xs = [?p]"
    and ready_cursor: "cursor ready_xs = Some ?p" .
  have ready_root: "sr_ready R 2 \<in> set (p2_physical_roots R)"
    by (simp add: p2_physical_roots_def)
  have pending_root: "sr_pending R \<in> set (p2_physical_roots R)"
    by (simp add: p2_physical_roots_def)
  have physical_distinct: "distinct (p2_physical_roots R)"
    using footprint unfolding p2_source_footprint_def by blast
  have roots_distinct: "sr_ready R 2 \<noteq> sr_pending R"
    using physical_distinct by (simp add: p2_physical_roots_def)
  have roots_disjoint:
    "raw_list_region ?ready \<inter> raw_list_region ?pending = {}"
    by (rule p2_source_footprint_raw_roots_disjointD[
          OF footprint ready_root pending_root roots_distinct])
  have item_pending_disjoint:
    "raw_item_region ?p \<inter> raw_list_region ?pending = {}"
    by (rule p2_source_footprint_generic_item_root_disjointD[
          OF footprint _ pending_root]) simp
  have remove_pending:
    "h_val ?hr ?pending = h_val ?h ?pending"
    by (rule raw_remove_singleton_preserves_disjoint_list[
          OF ready_rel ready_ring roots_disjoint item_pending_disjoint])
  have wake_pending:
    "h_val (p2_wake_key_heap ?hr D) ?pending = h_val ?hr ?pending"
    by (rule p2_wake_key_heap_raw_root_frame[
          OF footprint pending_root])
  show ?thesis
    using remove_pending wake_pending
    by (simp only: p2_remove_then_wake_heap_def)
qed

lemma p2_delayed_a_insert_pending_frame:
  assumes footprint: "p2_source_footprint D R h0"
  shows
    "h_val
       (raw_ordered_insert_empty_heap h
         (abi_list_ptr (sr_delayed_a R))
         (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)))
       (abi_list_ptr (sr_pending R)) =
     h_val h (abi_list_ptr (sr_pending R))"
proof -
  have delayed_root:
    "sr_delayed_a R \<in> set (p2_physical_roots R)"
    by (simp add: p2_physical_roots_def)
  have pending_root: "sr_pending R \<in> set (p2_physical_roots R)"
    by (simp add: p2_physical_roots_def)
  have physical_distinct: "distinct (p2_physical_roots R)"
    using footprint unfolding p2_source_footprint_def by blast
  have roots_distinct: "sr_delayed_a R \<noteq> sr_pending R"
    using physical_distinct by (simp add: p2_physical_roots_def)
  have roots_disjoint:
    "raw_list_region (abi_list_ptr (sr_delayed_a R)) \<inter>
       raw_list_region (abi_list_ptr (sr_pending R)) = {}"
    by (rule p2_source_footprint_raw_roots_disjointD[
          OF footprint delayed_root pending_root roots_distinct])
  have item_pending_disjoint:
    "raw_item_region
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)) \<inter>
       raw_list_region (abi_list_ptr (sr_pending R)) = {}"
    by (rule p2_source_footprint_generic_item_root_disjointD[
          OF footprint _ pending_root]) simp
  show ?thesis
    by (rule raw_ordered_insert_empty_heap_preserves_disjoint_list[
          OF roots_disjoint item_pending_disjoint])
qed

definition p2_remove_wake_insert_heap ::
  "heap_mem \<Rightarrow> p2_tid scheduler_decode \<Rightarrow>
   scheduler_roots \<Rightarrow> heap_mem"
where
  "p2_remove_wake_insert_heap h D R =
     raw_ordered_insert_empty_heap
       (p2_remove_then_wake_heap h D)
       (abi_list_ptr (sr_delayed_a R))
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))"

lemma p2_remove_wake_insert_pending_frame:
  fixes s :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R s p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))"
  shows
    "h_val
       (p2_remove_wake_insert_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)) D R)
       (abi_list_ptr (sr_pending R)) =
     h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
       (abi_list_ptr (sr_pending R))"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)"
  let ?hk = "p2_remove_then_wake_heap ?h D"
  have remove_wake:
    "h_val ?hk (abi_list_ptr (sr_pending R)) =
     h_val ?h (abi_list_ptr (sr_pending R))"
    by (rule p2_remove_then_wake_pending_frame[
          OF decode lists footprint])
  have insert:
    "h_val
       (raw_ordered_insert_empty_heap ?hk
         (abi_list_ptr (sr_delayed_a R))
         (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)))
       (abi_list_ptr (sr_pending R)) =
     h_val ?hk (abi_list_ptr (sr_pending R))"
    by (rule p2_delayed_a_insert_pending_frame[OF footprint])
  show ?thesis
    using insert remove_wake
    by (simp only: p2_remove_wake_insert_heap_def)
qed

lemma p2_remove_wake_insert_pending_raw_count_zero:
  fixes s :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R s p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))"
  shows
    "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
       (h_val
         (p2_remove_wake_insert_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)) D R)
         (abi_list_ptr (sr_pending R))) = 0"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)"
  let ?pending = "abi_list_ptr (sr_pending R)"
  from p2_pre_pending_raw_emptyE[OF lists]
  obtain pending_xs where
      pending_rel: "raw_xlist_rel ?h ?pending pending_xs"
    and pending_ring: "ring pending_xs = []"
    and pending_cursor: "cursor pending_xs = None" .
  have initial_count:
    "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
       (h_val ?h ?pending) = 0"
    using raw_xlist_rel_empty_facts[OF pending_rel pending_ring]
    by blast
  have frame:
    "h_val (p2_remove_wake_insert_heap ?h D R) ?pending =
     h_val ?h ?pending"
    by (rule p2_remove_wake_insert_pending_frame[
          OF decode lists footprint])
  show ?thesis using initial_count frame by simp
qed

lemma p2_remove_wake_insert_pending_scheduler_count_zero:
  fixes s :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R s p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))"
  shows
    "Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
       (h_val
         (p2_remove_wake_insert_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)) D R)
         Scheduler_V611_Parse.xPendingReadyList_') = 0"
proof -
  let ?hf =
    "p2_remove_wake_insert_heap
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)) D R"
  have raw_count:
    "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
       (h_val ?hf (abi_list_ptr (sr_pending R))) = 0"
    by (rule p2_remove_wake_insert_pending_raw_count_zero[
          OF decode lists footprint])
  have scheduler_count:
    "Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
       (h_val ?hf (sr_pending R)) = 0"
    using raw_count by (simp only: abi_list_count_h_val)
  have roots: "R = generated_scheduler_roots"
    by (rule p2_source_footprint_generated_rootsD[OF footprint])
  show ?thesis using scheduler_count roots by simp
qed

lemma p2_pending_ready_guard:
  assumes footprint: "p2_source_footprint D R h"
  shows "c_guard Scheduler_V611_Parse.xPendingReadyList_'"
proof -
  have pending_root: "sr_pending R \<in> set (p2_physical_roots R)"
    by (simp add: p2_physical_roots_def)
  have raw_guard: "c_guard (abi_list_ptr (sr_pending R))"
    by (rule p2_source_footprint_raw_root_guardD[
          OF footprint pending_root])
  have scheduler_guard: "c_guard (sr_pending R)"
    using raw_guard by (simp add: abi_list_ptr_c_guard)
  have roots: "R = generated_scheduler_roots"
    by (rule p2_source_footprint_generated_rootsD[OF footprint])
  show ?thesis using scheduler_guard roots by simp
qed

end
