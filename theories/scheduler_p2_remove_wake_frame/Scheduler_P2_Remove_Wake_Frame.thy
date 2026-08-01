theory Scheduler_P2_Remove_Wake_Frame
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Remove_Cross_List.Scheduler_P2_Remove_Cross_List"
begin

text \<open>
  Compose the checked ready-list removal transformer with the checked wake-key
  write.  The result is the exact ordered-empty entry package needed by the
  scheduler-universe delayed-list insertion leaf.
\<close>

lemma raw_xlist_rel_empty_h_val_cong:
  assumes rel: "raw_xlist_rel h lp xs"
    and empty: "ring xs = []"
    and list_same: "h_val h' lp = h_val h lp"
  shows "raw_xlist_rel h' lp xs"
  using rel empty list_same
  by (simp add: raw_xlist_rel_def raw_xlist_view_def
      raw_cursor_at_def raw_ring_links_def raw_edge_pairs_def
      raw_next_at_def raw_prev_at_def)

lemma p2_remove_then_wake_delayed_a_ordered_emptyE:
  fixes s :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R s p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))"
  obtains rx where
    "raw_xlist_rel
       (p2_remove_then_wake_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)) D)
       (abi_list_ptr (sr_delayed_a R)) rx"
    "ring rx = []"
    "cursor rx = None"
    "raw_sentinel_max
       (p2_remove_then_wake_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)) D)
       (abi_list_ptr (sr_delayed_a R))"
    "raw_fresh_for_insert
       (abi_list_ptr (sr_delayed_a R)) (ring rx)
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))"
    "raw_key_at
       (p2_remove_then_wake_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)) D)
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)) = 7"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)"
  let ?ready = "abi_list_ptr (sr_ready R 2)"
  let ?delayed = "abi_list_ptr (sr_delayed_a R)"
  let ?p = "abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)"
  let ?hr = "raw_remove_concrete_heap ?h ?p"
  let ?hk = "p2_wake_key_heap ?hr D"
  from p2_pre_ready2_raw_singletonE[OF decode lists]
  obtain ready_xs where
      ready_rel: "raw_xlist_rel ?h ?ready ready_xs"
    and ready_ring: "ring ready_xs = [?p]"
    and ready_cursor: "cursor ready_xs = Some ?p" .
  from p2_pre_delayed_a_ordered_emptyE[OF lists footprint]
  obtain rx where
      delayed_rel: "raw_xlist_rel ?h ?delayed rx"
    and empty: "ring rx = []"
    and cursor: "cursor rx = None"
    and sentinel: "raw_sentinel_max ?h ?delayed"
    and fresh:
      "raw_fresh_for_insert ?delayed (ring rx) ?p" .
  have ready_root: "sr_ready R 2 \<in> set (p2_physical_roots R)"
    by (simp add: p2_physical_roots_def)
  have delayed_root:
    "sr_delayed_a R \<in> set (p2_physical_roots R)"
    by (simp add: p2_physical_roots_def)
  have physical_distinct: "distinct (p2_physical_roots R)"
    using footprint unfolding p2_source_footprint_def by blast
  have roots_distinct: "sr_ready R 2 \<noteq> sr_delayed_a R"
    using physical_distinct by (simp add: p2_physical_roots_def)
  have roots_disjoint:
    "raw_list_region ?ready \<inter> raw_list_region ?delayed = {}"
    by (rule p2_source_footprint_raw_roots_disjointD[
          OF footprint ready_root delayed_root roots_distinct])
  have item_delayed_disjoint:
    "raw_item_region ?p \<inter> raw_list_region ?delayed = {}"
    by (rule p2_source_footprint_generic_item_root_disjointD[
          OF footprint _ delayed_root]) simp
  have remove_delayed:
    "h_val ?hr ?delayed = h_val ?h ?delayed"
    by (rule raw_remove_singleton_preserves_disjoint_list[
          OF ready_rel ready_ring roots_disjoint item_delayed_disjoint])
  have key_delayed:
    "h_val ?hk ?delayed = h_val ?hr ?delayed"
    by (rule p2_wake_key_heap_raw_root_frame[
          OF footprint delayed_root])
  have final_delayed:
    "h_val ?hk ?delayed = h_val ?h ?delayed"
    using remove_delayed key_delayed by simp
  have final_rel: "raw_xlist_rel ?hk ?delayed rx"
    by (rule raw_xlist_rel_empty_h_val_cong[
          OF delayed_rel empty final_delayed])
  have sentinel_key_same:
    "raw_key_at ?hk (raw_end_item ?delayed) =
     raw_key_at ?h (raw_end_item ?delayed)"
    by (rule raw_ordered_sentinel_key_cong[OF final_delayed])
  have final_sentinel: "raw_sentinel_max ?hk ?delayed"
    using sentinel sentinel_key_same
    by (simp add: raw_sentinel_max_def)
  have final_key: "raw_key_at ?hk ?p = 7"
    by (rule p2_wake_key_heap_raw_key_7[OF footprint])
  show ?thesis
    apply (rule that[where rx=rx])
    using final_rel empty cursor final_sentinel fresh final_key
    by (simp_all only: p2_remove_then_wake_heap_def)
qed

end
