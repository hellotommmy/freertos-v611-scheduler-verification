theory Scheduler_P2_Post_Relation
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Insert_Refinement.Scheduler_P2_Insert_Refinement"
begin

text \<open>
  Pure postrelation assembly for the positive-delay P2 path.  This theory
  opens no generated C body.  Its first rung turns the already checked exact
  removal transformer into a raw-list refinement, then specialises that fact
  to the ready-priority-2 singleton of p2_pre.
\<close>

lemma raw_remove_concrete_heap_refines:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_xlist_rel (raw_remove_concrete_heap h p) lp
       (list_remove_abs p xs)"
proof -
  have count:
    "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
       (h_val (raw_remove_concrete_heap h p) lp) =
     List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
       (h_val h lp) - 1"
    by (rule raw_remove_concrete_heap_count_effect[OF rel member])
  have index:
    "List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C
       (h_val (raw_remove_concrete_heap h p) lp) =
       (if List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C
             (h_val h lp) = p
        then raw_prev_at h lp p
        else List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C
             (h_val h lp))"
    by (rule raw_remove_concrete_heap_index_effect[OF rel member])
  have topology:
    "raw_ring_links (raw_remove_concrete_heap h p) lp
       (remove1 p (ring xs))"
    by (rule raw_remove_concrete_heap_topology_effect[OF rel member])
  have payload:
    "\<forall>q \<in> set (remove1 p (ring xs)).
       raw_key_at (raw_remove_concrete_heap h p) q = raw_key_at h q \<and>
       List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
         (h_val (raw_remove_concrete_heap h p) q) =
       List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
         (h_val h q)"
    by (rule raw_remove_concrete_heap_payload_effect[OF rel member])
  have effect:
    "raw_remove_effect h (raw_remove_concrete_heap h p) lp xs p"
    using count index topology payload
    by (simp add: raw_remove_effect_def)
  show ?thesis
    by (rule raw_remove_effect_refines[OF rel member effect])
qed

lemma p2_remove_ready2_refines_empty:
  fixes c :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R c p2_pre"
  shows
    "sched_xlist_rel (sd_node_decode D)
       (raw_remove_concrete_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)))
       (abi_list_ptr (sr_ready R 2)) (sa_ready p2_post 2)"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?lp = "abi_list_ptr (sr_ready R 2)"
  let ?p = "abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)"
  from p2_pre_ready2_raw_singletonE[OF decode lists]
  obtain rx where
      rel: "raw_xlist_rel ?h ?lp rx"
    and singleton: "ring rx = [?p]"
    and cursor: "cursor rx = Some ?p" .
  have member: "?p \<in> set (ring rx)"
    using singleton by simp
  have raw_post:
    "raw_xlist_rel (raw_remove_concrete_heap ?h ?p) ?lp
       (list_remove_abs ?p rx)"
    by (rule raw_remove_concrete_heap_refines[OF rel member])
  have raw_ring: "ring (list_remove_abs ?p rx) = []"
    using singleton by (simp add: list_remove_abs_def)
  have raw_cursor: "cursor (list_remove_abs ?p rx) = None"
    using singleton cursor by (simp add: list_remove_abs_def)
  have abs_ring: "ring (sa_ready p2_post 2) = []"
    by (simp add: p2_post_def empty_node_ring_def)
  have abs_cursor: "cursor (sa_ready p2_post 2) = None"
    by (simp add: p2_post_def empty_node_ring_def)
  show ?thesis
    by (rule sched_xlist_rel_emptyI[
          OF raw_post raw_ring raw_cursor abs_ring abs_cursor])
qed

lemma sched_xlist_rel_empty_h_val_cong:
  assumes sched: "sched_xlist_rel D h lp q"
    and abs_ring: "ring q = []"
    and abs_cursor: "cursor q = None"
    and list_same: "h_val h' lp = h_val h lp"
  shows "sched_xlist_rel D h' lp q"
proof -
  from sched_xlist_rel_emptyE[OF sched abs_ring abs_cursor]
  obtain rx where
      raw: "raw_xlist_rel h lp rx"
    and raw_ring: "ring rx = []"
    and raw_cursor: "cursor rx = None" .
  have raw_post: "raw_xlist_rel h' lp rx"
    by (rule raw_xlist_rel_empty_h_val_cong[
          OF raw raw_ring list_same])
  show ?thesis
    by (rule sched_xlist_rel_emptyI[
          OF raw_post raw_ring raw_cursor abs_ring abs_cursor])
qed

lemma p2_remove_wake_insert_other_root_frame:
  fixes c :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R c p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
    and target: "lq \<in> set (p2_physical_roots R)"
    and not_ready: "sr_ready R 2 \<noteq> lq"
    and not_delayed: "sr_delayed_a R \<noteq> lq"
  shows
    "h_val
       (p2_remove_wake_insert_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) D R)
       (abi_list_ptr lq) =
     h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (abi_list_ptr lq)"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?ready = "abi_list_ptr (sr_ready R 2)"
  let ?delayed = "abi_list_ptr (sr_delayed_a R)"
  let ?target = "abi_list_ptr lq"
  let ?p = "abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)"
  let ?hr = "raw_remove_concrete_heap ?h ?p"
  let ?hk = "p2_remove_then_wake_heap ?h D"
  from p2_pre_ready2_raw_singletonE[OF decode lists]
  obtain ready_xs where
      ready_rel: "raw_xlist_rel ?h ?ready ready_xs"
    and ready_ring: "ring ready_xs = [?p]"
    and ready_cursor: "cursor ready_xs = Some ?p" .
  have ready_root: "sr_ready R 2 \<in> set (p2_physical_roots R)"
    by (simp add: p2_physical_roots_def)
  have delayed_root:
    "sr_delayed_a R \<in> set (p2_physical_roots R)"
    by (simp add: p2_physical_roots_def)
  have ready_target_disjoint:
    "raw_list_region ?ready \<inter> raw_list_region ?target = {}"
    by (rule p2_source_footprint_raw_roots_disjointD[
          OF footprint ready_root target not_ready])
  have delayed_target_disjoint:
    "raw_list_region ?delayed \<inter> raw_list_region ?target = {}"
    by (rule p2_source_footprint_raw_roots_disjointD[
          OF footprint delayed_root target not_delayed])
  have item_target_disjoint:
    "raw_item_region ?p \<inter> raw_list_region ?target = {}"
    by (rule p2_source_footprint_generic_item_root_disjointD[
          OF footprint _ target]) simp
  have remove_frame: "h_val ?hr ?target = h_val ?h ?target"
    by (rule raw_remove_singleton_preserves_disjoint_list[
          OF ready_rel ready_ring ready_target_disjoint
             item_target_disjoint])
  have wake_frame:
    "h_val (p2_wake_key_heap ?hr D) ?target = h_val ?hr ?target"
    by (rule p2_wake_key_heap_raw_root_frame[OF footprint target])
  have remove_wake_frame: "h_val ?hk ?target = h_val ?h ?target"
    using remove_frame wake_frame
    by (simp only: p2_remove_then_wake_heap_def)
  have insert_frame:
    "h_val
       (raw_ordered_insert_empty_heap ?hk ?delayed ?p) ?target =
     h_val ?hk ?target"
    by (rule raw_ordered_insert_empty_heap_preserves_disjoint_list[
          OF delayed_target_disjoint item_target_disjoint])
  show ?thesis
    using insert_frame remove_wake_frame
    by (simp only: p2_remove_wake_insert_heap_def)
qed

lemma p2_remove_wake_insert_preserves_empty_root:
  fixes c :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R c p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
    and target: "lq \<in> set (p2_physical_roots R)"
    and not_ready: "sr_ready R 2 \<noteq> lq"
    and not_delayed: "sr_delayed_a R \<noteq> lq"
    and sched:
      "sched_xlist_rel (sd_node_decode D)
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
        (abi_list_ptr lq) q"
    and abs_ring: "ring q = []"
    and abs_cursor: "cursor q = None"
  shows
    "sched_xlist_rel (sd_node_decode D)
       (p2_remove_wake_insert_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) D R)
       (abi_list_ptr lq) q"
proof -
  have frame:
    "h_val
       (p2_remove_wake_insert_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) D R)
       (abi_list_ptr lq) =
     h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (abi_list_ptr lq)"
    by (rule p2_remove_wake_insert_other_root_frame[
          OF decode lists footprint target not_ready not_delayed])
  show ?thesis
    by (rule sched_xlist_rel_empty_h_val_cong[
          OF sched abs_ring abs_cursor frame])
qed

lemma raw_remove_singleton_preserves_disjoint_item:
  assumes rel: "raw_xlist_rel h lp xs"
    and singleton: "ring xs = [p]"
    and target_root:
      "raw_item_region q \<inter> raw_list_region lp = {}"
    and items:
      "raw_item_region p \<inter> raw_item_region q = {}"
  shows
    "h_val (raw_remove_concrete_heap h p) q = h_val h q"
proof -
  have member: "p \<in> set (ring xs)"
    using singleton by simp
  note fields = raw_remove_singleton_link_fields[OF rel singleton]
  let ?h1 = "raw_source_unlink_first h p"
  let ?hu = "raw_source_unlink_two h p"
  have first_subset:
    "raw_pointer_field_region
       (raw_previous_field_ptr
         (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxNext_C
           (h_val h p))) \<subseteq>
     raw_list_region lp"
    using fields raw_end_previous_field_region_subset_list[where lp=lp]
    by simp
  have first_disjoint:
    "raw_pointer_field_region
       (raw_previous_field_ptr
         (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxNext_C
           (h_val h p))) \<inter>
     raw_item_region q = {}"
    using first_subset target_root by blast
  have h1_target: "h_val ?h1 q = h_val h q"
    unfolding raw_source_unlink_first_def
    by (rule raw_pointer_field_update_preserves_disjoint_item[
          OF first_disjoint])
  have h1_item: "h_val ?h1 p = h_val h p"
    unfolding raw_source_unlink_first_def
    by (rule raw_remove_first_unlink_preserves_item[OF rel member])
  have second_subset:
    "raw_pointer_field_region
       (raw_next_field_ptr
         (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxPrevious_C
           (h_val ?h1 p))) \<subseteq>
     raw_list_region lp"
    using fields h1_item
      raw_end_next_field_region_subset_list[where lp=lp]
    by simp
  have second_disjoint:
    "raw_pointer_field_region
       (raw_next_field_ptr
         (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxPrevious_C
           (h_val ?h1 p))) \<inter>
     raw_item_region q = {}"
    using second_subset target_root by blast
  have unlink_target: "h_val ?hu q = h_val h q"
  proof -
    have "h_val ?hu q = h_val ?h1 q"
      unfolding raw_source_unlink_two_def
      by (rule raw_pointer_field_update_preserves_disjoint_item[
            OF second_disjoint])
    also have "... = h_val h q" by (rule h1_target)
    finally show ?thesis .
  qed
  let ?hi = "raw_remove_index_heap ?hu lp p"
  let ?hc = "raw_remove_container_heap ?hi p"
  have index_target: "h_val ?hi q = h_val ?hu q"
  proof (cases
      "List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C
         (h_val ?hu lp) = p")
    case True
    show ?thesis
      unfolding raw_remove_index_heap_def
      apply (simp only: if_P[OF True])
      by (rule
        List_V611_Raw_R6_Remove_Topology_Effect.raw_list_update_preserves_disjoint_item[
          OF target_root])
  next
    case False
    show ?thesis
      unfolding raw_remove_index_heap_def
      by (simp only: if_not_P[OF False])
  qed
  have container_target: "h_val ?hc q = h_val ?hi q"
    unfolding raw_remove_container_heap_def
    by (rule raw_item_update_preserves_disjoint_item[OF items])
  have count_target:
    "h_val (raw_remove_count_heap ?hc lp) q = h_val ?hc q"
    unfolding raw_remove_count_heap_def
    by (rule
      List_V611_Raw_R6_Remove_Topology_Effect.raw_list_update_preserves_disjoint_item[
        OF target_root])
  have suffix_target:
    "h_val (raw_remove_suffix_heap ?hu lp p) q = h_val ?hu q"
  proof -
    have
      "h_val (raw_remove_suffix_heap ?hu lp p) q =
       h_val (raw_remove_count_heap ?hc lp) q"
      by (simp only: raw_remove_suffix_heap_def)
    also have "... = h_val ?hc q" by (rule count_target)
    also have "... = h_val ?hi q" by (rule container_target)
    also have "... = h_val ?hu q" by (rule index_target)
    finally show ?thesis .
  qed
  have concrete:
    "raw_remove_concrete_heap h p = raw_remove_source_heap h lp p"
    by (rule raw_remove_concrete_heap_eq[OF rel member])
  show ?thesis
    using concrete suffix_target unlink_target
    by (simp only: raw_remove_source_heap_def)
qed

lemma raw_ordered_insert_empty_heap_preserves_disjoint_item:
  assumes target_root:
      "raw_item_region q \<inter> raw_list_region lp = {}"
    and items:
      "raw_item_region p \<inter> raw_item_region q = {}"
  shows
    "h_val (raw_ordered_insert_empty_heap h lp p) q = h_val h q"
proof -
  let ?e = "raw_end_item lp"
  let ?h1 = "raw_insert_next_heap h p ?e"
  let ?h2 = "raw_insert_previous_heap ?h1 ?e p"
  let ?h3 = "raw_insert_previous_heap ?h2 p ?e"
  let ?h4 = "raw_insert_next_heap ?h3 ?e p"
  let ?h5 = "raw_insert_container_heap ?h4 lp p"
  have p_next_disjoint:
    "raw_pointer_field_region (raw_next_field_ptr p) \<inter>
       raw_item_region q = {}"
    using raw_next_field_region_subset_item[where u=p] items by blast
  have p_previous_disjoint:
    "raw_pointer_field_region (raw_previous_field_ptr p) \<inter>
       raw_item_region q = {}"
    using raw_previous_field_region_subset_item[where u=p] items by blast
  have end_next_disjoint:
    "raw_pointer_field_region (raw_next_field_ptr ?e) \<inter>
       raw_item_region q = {}"
    using raw_end_next_field_region_subset_list[where lp=lp]
      target_root by blast
  have end_previous_disjoint:
    "raw_pointer_field_region (raw_previous_field_ptr ?e) \<inter>
       raw_item_region q = {}"
    using raw_end_previous_field_region_subset_list[where lp=lp]
      target_root by blast
  have h1_frame: "h_val ?h1 q = h_val h q"
    unfolding raw_insert_next_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_item[
          OF p_next_disjoint])
  have h2_frame: "h_val ?h2 q = h_val ?h1 q"
    unfolding raw_insert_previous_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_item[
          OF end_previous_disjoint])
  have h3_frame: "h_val ?h3 q = h_val ?h2 q"
    unfolding raw_insert_previous_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_item[
          OF p_previous_disjoint])
  have h4_frame: "h_val ?h4 q = h_val ?h3 q"
    unfolding raw_insert_next_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_item[
          OF end_next_disjoint])
  have h5_frame: "h_val ?h5 q = h_val ?h4 q"
    unfolding raw_insert_container_heap_def
    by (rule raw_item_update_preserves_disjoint_item[OF items])
  have h6_frame:
    "h_val (raw_insert_count_heap ?h5 lp) q = h_val ?h5 q"
    unfolding raw_insert_count_heap_def
    by (rule
      List_V611_Raw_R6_Remove_Topology_Effect.raw_list_update_preserves_disjoint_item[
        OF target_root])
  have
    "h_val (raw_ordered_insert_empty_heap h lp p) q =
     h_val (raw_insert_count_heap ?h5 lp) q"
    by (simp only: raw_ordered_insert_empty_heap_def Let_def)
  also have "... = h_val ?h5 q" by (rule h6_frame)
  also have "... = h_val ?h4 q" by (rule h5_frame)
  also have "... = h_val ?h3 q" by (rule h4_frame)
  also have "... = h_val ?h2 q" by (rule h3_frame)
  also have "... = h_val ?h1 q" by (rule h2_frame)
  also have "... = h_val h q" by (rule h1_frame)
  finally show ?thesis .
qed

lemma scheduler_generic_item_key_heap_preserves_disjoint_raw_item:
  assumes guard: "c_guard (abi_generic_list_item_ptr tp)"
    and disjoint:
      "raw_item_region (abi_generic_list_item_ptr tp) \<inter>
       raw_item_region q = {}"
  shows
    "h_val (scheduler_generic_item_key_heap h tp wake) q = h_val h q"
  apply (subst scheduler_generic_item_key_heap_raw_whole[OF guard])
  by (rule raw_item_update_preserves_disjoint_item[OF disjoint])

lemma p2_source_footprint_run_idle_generic_items_disjointD:
  assumes footprint: "p2_source_footprint D R h"
  shows
    "raw_item_region
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)) \<inter>
     raw_item_region
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_IDLE)) = {}"
proof -
  have idle_run_distinct:
    "sd_tcb_ptr D P2_IDLE \<noteq> sd_tcb_ptr D P2_RUN"
    by (rule p2_source_footprint_tcb_ptrs_distinctD[OF footprint])
  have run_idle_distinct:
    "sd_tcb_ptr D P2_RUN \<noteq> sd_tcb_ptr D P2_IDLE"
  proof
    assume equal: "sd_tcb_ptr D P2_RUN = sd_tcb_ptr D P2_IDLE"
    have "sd_tcb_ptr D P2_IDLE = sd_tcb_ptr D P2_RUN"
      by (rule sym[OF equal])
    with idle_run_distinct show False by contradiction
  qed
  have tcb_pairwise:
    "\<forall>tp \<in> set (p2_tcb_ptrs D).
       \<forall>tq \<in> set (p2_tcb_ptrs D).
        tp \<noteq> tq \<longrightarrow>
        scheduler_tcb_region tp \<inter> scheduler_tcb_region tq = {}"
    using footprint unfolding p2_source_footprint_def by blast
  have tcb_disjoint:
    "scheduler_tcb_region (sd_tcb_ptr D P2_RUN) \<inter>
     scheduler_tcb_region (sd_tcb_ptr D P2_IDLE) = {}"
    using tcb_pairwise run_idle_distinct
    by (simp add: p2_tcb_ptrs_def)
  have run_subset:
    "scheduler_item_region
       (scheduler_generic_item_ptr (sd_tcb_ptr D P2_RUN)) \<subseteq>
     scheduler_tcb_region (sd_tcb_ptr D P2_RUN)"
    using footprint by (auto simp: p2_source_footprint_def)
  have idle_subset:
    "scheduler_item_region
       (scheduler_generic_item_ptr (sd_tcb_ptr D P2_IDLE)) \<subseteq>
     scheduler_tcb_region (sd_tcb_ptr D P2_IDLE)"
    using footprint by (auto simp: p2_source_footprint_def)
  have scheduler_disjoint:
    "scheduler_item_region
       (scheduler_generic_item_ptr (sd_tcb_ptr D P2_RUN)) \<inter>
     scheduler_item_region
       (scheduler_generic_item_ptr (sd_tcb_ptr D P2_IDLE)) = {}"
    using run_subset idle_subset tcb_disjoint by blast
  have run_region:
    "raw_item_region
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)) =
     scheduler_item_region
       (scheduler_generic_item_ptr (sd_tcb_ptr D P2_RUN))"
    using abi_item_region_eq[
      where p="scheduler_generic_item_ptr (sd_tcb_ptr D P2_RUN)"]
    by simp
  have idle_region:
    "raw_item_region
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_IDLE)) =
     scheduler_item_region
       (scheduler_generic_item_ptr (sd_tcb_ptr D P2_IDLE))"
    using abi_item_region_eq[
      where p="scheduler_generic_item_ptr (sd_tcb_ptr D P2_IDLE)"]
    by simp
  show ?thesis using scheduler_disjoint run_region idle_region by simp
qed

lemma p2_wake_key_heap_idle_item_frame:
  assumes footprint: "p2_source_footprint D R h0"
  shows
    "h_val (p2_wake_key_heap h D)
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_IDLE)) =
     h_val h (abi_generic_list_item_ptr (sd_tcb_ptr D P2_IDLE))"
proof -
  have guard:
    "c_guard (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))"
    by (rule p2_source_footprint_generic_raw_guardD[OF footprint]) simp
  have disjoint:
    "raw_item_region
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)) \<inter>
     raw_item_region
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_IDLE)) = {}"
    by (rule p2_source_footprint_run_idle_generic_items_disjointD[
          OF footprint])
  show ?thesis
    unfolding p2_wake_key_heap_def
    by (rule scheduler_generic_item_key_heap_preserves_disjoint_raw_item[
          OF guard disjoint])
qed

lemma p2_neq_sym:
  assumes distinct: "x \<noteq> y"
  shows "y \<noteq> x"
proof
  assume equal: "y = x"
  have "x = y" by (rule sym[OF equal])
  with distinct show False by contradiction
qed

lemma p2_remove_wake_insert_delayed_a_final:
  fixes c :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R c p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
  shows
    "sched_xlist_rel (sd_node_decode D)
       (p2_remove_wake_insert_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) D R)
       (abi_list_ptr (sr_delayed_a R)) (sa_delayed_a p2_post)"
proof -
  have delayed:
    "sched_xlist_rel (sd_node_decode D)
       (raw_ordered_insert_empty_heap
         (p2_remove_then_wake_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) D)
         (abi_list_ptr (sr_delayed_a R))
         (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)))
       (abi_list_ptr (sr_delayed_a R)) p2_run_delayed"
    by (rule p2_remove_wake_insert_delayed_a_refines[
          OF decode lists footprint])
  show ?thesis
    using delayed
    by (simp add: p2_remove_wake_insert_heap_def p2_post_def)
qed

lemma p2_remove_wake_insert_empty_components:
  fixes c :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R c p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
  shows
    "sched_xlist_rel (sd_node_decode D)
       (p2_remove_wake_insert_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) D R)
       (abi_list_ptr (sr_ready R 1)) (sa_ready p2_post 1) \<and>
     sched_xlist_rel (sd_node_decode D)
       (p2_remove_wake_insert_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) D R)
       (abi_list_ptr (sr_ready R 3)) (sa_ready p2_post 3) \<and>
     sched_xlist_rel (sd_node_decode D)
       (p2_remove_wake_insert_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) D R)
       (abi_list_ptr (sr_delayed_b R)) (sa_delayed_b p2_post) \<and>
     sched_xlist_rel (sd_node_decode D)
       (p2_remove_wake_insert_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) D R)
       (abi_list_ptr (sr_pending R)) (sa_pending p2_post) \<and>
     sched_xlist_rel (sd_node_decode D)
       (p2_remove_wake_insert_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) D R)
       (abi_list_ptr (sr_suspended R)) (sa_suspended p2_post)"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?hf = "p2_remove_wake_insert_heap ?h D R"
  have physical_distinct: "distinct (p2_physical_roots R)"
    using footprint unfolding p2_source_footprint_def by blast
  have r1_r2: "sr_ready R 1 \<noteq> sr_ready R 2"
    using physical_distinct by (simp add: p2_physical_roots_def)
  have r2_r1: "sr_ready R 2 \<noteq> sr_ready R 1"
    by (rule p2_neq_sym[OF r1_r2])
  have r1_da: "sr_ready R 1 \<noteq> sr_delayed_a R"
    using physical_distinct by (simp add: p2_physical_roots_def)
  have da_r1: "sr_delayed_a R \<noteq> sr_ready R 1"
    by (rule p2_neq_sym[OF r1_da])
  have r2_r3: "sr_ready R 2 \<noteq> sr_ready R 3"
    using physical_distinct by (simp add: p2_physical_roots_def)
  have r3_da: "sr_ready R 3 \<noteq> sr_delayed_a R"
    using physical_distinct by (simp add: p2_physical_roots_def)
  have da_r3: "sr_delayed_a R \<noteq> sr_ready R 3"
    by (rule p2_neq_sym[OF r3_da])
  have r2_db: "sr_ready R 2 \<noteq> sr_delayed_b R"
    using physical_distinct by (simp add: p2_physical_roots_def)
  have da_db: "sr_delayed_a R \<noteq> sr_delayed_b R"
    using physical_distinct by (simp add: p2_physical_roots_def)
  have r2_pending: "sr_ready R 2 \<noteq> sr_pending R"
    using physical_distinct by (simp add: p2_physical_roots_def)
  have da_pending: "sr_delayed_a R \<noteq> sr_pending R"
    using physical_distinct by (simp add: p2_physical_roots_def)
  have r2_suspended: "sr_ready R 2 \<noteq> sr_suspended R"
    using physical_distinct by (simp add: p2_physical_roots_def)
  have da_suspended: "sr_delayed_a R \<noteq> sr_suspended R"
    using physical_distinct by (simp add: p2_physical_roots_def)
  have ready_all:
    "\<forall>p<4. sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr (sr_ready R p)) (sa_ready p2_pre p)"
    using lists unfolding scheduler_lists_rel_def Let_def by blast
  have ready1_raw:
    "sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr (sr_ready R 1)) (sa_ready p2_pre 1)"
    by (rule ready_all[rule_format]) simp
  have ready1_pre:
    "sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr (sr_ready R 1)) empty_node_ring"
    using ready1_raw by (simp add: p2_pre_def)
  have ready3_raw:
    "sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr (sr_ready R 3)) (sa_ready p2_pre 3)"
    by (rule ready_all[rule_format]) simp
  have ready3_pre:
    "sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr (sr_ready R 3)) empty_node_ring"
    using ready3_raw by (simp add: p2_pre_def)
  have delayed_b_raw:
    "sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr (sr_delayed_b R)) (sa_delayed_b p2_pre)"
    using lists unfolding scheduler_lists_rel_def Let_def by blast
  have delayed_b_pre:
    "sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr (sr_delayed_b R)) empty_node_ring"
    using delayed_b_raw by (simp add: p2_pre_def)
  have pending_raw:
    "sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr (sr_pending R)) (sa_pending p2_pre)"
    using lists unfolding scheduler_lists_rel_def Let_def by blast
  have pending_pre:
    "sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr (sr_pending R)) empty_node_ring"
    using pending_raw by (simp add: p2_pre_def)
  have suspended_raw:
    "sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr (sr_suspended R)) (sa_suspended p2_pre)"
    using lists unfolding scheduler_lists_rel_def Let_def by blast
  have suspended_pre:
    "sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr (sr_suspended R)) empty_node_ring"
    using suspended_raw by (simp add: p2_pre_def)
  have ready1_empty:
    "sched_xlist_rel (sd_node_decode D) ?hf
       (abi_list_ptr (sr_ready R 1)) empty_node_ring"
    apply (rule p2_remove_wake_insert_preserves_empty_root[
        OF decode lists footprint])
    apply (simp add: p2_physical_roots_def)
    apply (rule r2_r1)
    apply (rule da_r1)
    apply (rule ready1_pre)
    apply (simp_all add: empty_node_ring_def)
    done
  have ready3_empty:
    "sched_xlist_rel (sd_node_decode D) ?hf
       (abi_list_ptr (sr_ready R 3)) empty_node_ring"
    apply (rule p2_remove_wake_insert_preserves_empty_root[
        OF decode lists footprint])
    apply (simp add: p2_physical_roots_def)
    apply (rule r2_r3)
    apply (rule da_r3)
    apply (rule ready3_pre)
    apply (simp_all add: empty_node_ring_def)
    done
  have delayed_b_empty:
    "sched_xlist_rel (sd_node_decode D) ?hf
       (abi_list_ptr (sr_delayed_b R)) empty_node_ring"
    apply (rule p2_remove_wake_insert_preserves_empty_root[
        OF decode lists footprint])
    apply (simp add: p2_physical_roots_def)
    apply (rule r2_db)
    apply (rule da_db)
    apply (rule delayed_b_pre)
    apply (simp_all add: empty_node_ring_def)
    done
  have pending_empty:
    "sched_xlist_rel (sd_node_decode D) ?hf
       (abi_list_ptr (sr_pending R)) empty_node_ring"
    apply (rule p2_remove_wake_insert_preserves_empty_root[
        OF decode lists footprint])
    apply (simp add: p2_physical_roots_def)
    apply (rule r2_pending)
    apply (rule da_pending)
    apply (rule pending_pre)
    apply (simp_all add: empty_node_ring_def)
    done
  have suspended_empty:
    "sched_xlist_rel (sd_node_decode D) ?hf
       (abi_list_ptr (sr_suspended R)) empty_node_ring"
    apply (rule p2_remove_wake_insert_preserves_empty_root[
        OF decode lists footprint])
    apply (simp add: p2_physical_roots_def)
    apply (rule r2_suspended)
    apply (rule da_suspended)
    apply (rule suspended_pre)
    apply (simp_all add: empty_node_ring_def)
    done
  show ?thesis
    using ready1_empty ready3_empty delayed_b_empty pending_empty
      suspended_empty
    by (simp add: p2_post_def)
qed

lemma raw_xlist_rel_singleton_h_val_cong:
  assumes rel: "raw_xlist_rel h lp xs"
    and singleton: "ring xs = [p]"
    and list_same: "h_val h' lp = h_val h lp"
    and item_same: "h_val h' p = h_val h p"
  shows "raw_xlist_rel h' lp xs"
proof -
  have layout: "raw_xlist_layout lp [p]"
    using rel singleton by (simp add: raw_xlist_rel_def)
  have not_end: "p \<noteq> raw_end_item lp"
    using layout by (auto simp: raw_xlist_layout_def)
  have wf: "xlist_wf xs"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have count:
    "unat
       (List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
         (h_val h' lp)) = length (ring xs)"
    using raw_xlist_rel_countD[OF rel] list_same by simp
  have cursor: "cursor xs = raw_cursor_at h' lp"
    using raw_xlist_rel_cursorD[OF rel] list_same
    by (simp add: raw_cursor_at_def)
  have old_links: "raw_ring_links h lp [p]"
    using rel singleton
    by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have link_fields:
    "List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxNext_C
       (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
         (h_val h lp)) = p \<and>
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxPrevious_C
       (h_val h p) = raw_end_item lp \<and>
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxNext_C
       (h_val h p) = raw_end_item lp \<and>
     List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxPrevious_C
       (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
         (h_val h lp)) = p"
    using iffD1[OF raw_ring_links_singleton_iff[OF not_end] old_links] .
  have new_links: "raw_ring_links h' lp [p]"
    apply (rule iffD2[OF raw_ring_links_singleton_iff[OF not_end]])
    using link_fields list_same item_same by simp
  have old_live:
    "item_key xs p = raw_key_at h p \<and>
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
       (h_val h p) =
       PTR_COERCE(List_V611_Raw_Skip_Translation.xLIST_C \<rightarrow> unit) lp"
    by (rule raw_xlist_rel_live_itemD[OF rel]) (simp add: singleton)
  have new_live:
    "item_key xs p = raw_key_at h' p \<and>
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
       (h_val h' p) =
       PTR_COERCE(List_V611_Raw_Skip_Translation.xLIST_C \<rightarrow> unit) lp"
    using old_live item_same by (simp add: raw_key_at_def)
  show ?thesis
    using layout wf count cursor new_links new_live singleton
    by (simp add: raw_xlist_rel_def raw_xlist_view_def)
qed

lemma p2_remove_wake_insert_idle_item_frame:
  fixes c :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R c p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
  shows
    "h_val
       (p2_remove_wake_insert_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) D R)
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_IDLE)) =
     h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_IDLE))"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?ready = "abi_list_ptr (sr_ready R 2)"
  let ?delayed = "abi_list_ptr (sr_delayed_a R)"
  let ?run = "abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)"
  let ?idle = "abi_generic_list_item_ptr (sd_tcb_ptr D P2_IDLE)"
  let ?hr = "raw_remove_concrete_heap ?h ?run"
  let ?hk = "p2_remove_then_wake_heap ?h D"
  from p2_pre_ready2_raw_singletonE[OF decode lists]
  obtain ready_xs where
      ready_rel: "raw_xlist_rel ?h ?ready ready_xs"
    and ready_ring: "ring ready_xs = [?run]"
    and ready_cursor: "cursor ready_xs = Some ?run" .
  have ready_root: "sr_ready R 2 \<in> set (p2_physical_roots R)"
    by (simp add: p2_physical_roots_def)
  have delayed_root:
    "sr_delayed_a R \<in> set (p2_physical_roots R)"
    by (simp add: p2_physical_roots_def)
  have idle_ready_disjoint:
    "raw_item_region ?idle \<inter> raw_list_region ?ready = {}"
    by (rule p2_source_footprint_generic_item_root_disjointD[
          OF footprint _ ready_root]) simp
  have run_idle_disjoint:
    "raw_item_region ?run \<inter> raw_item_region ?idle = {}"
    by (rule p2_source_footprint_run_idle_generic_items_disjointD[
          OF footprint])
  have remove_frame: "h_val ?hr ?idle = h_val ?h ?idle"
    by (rule raw_remove_singleton_preserves_disjoint_item[
          OF ready_rel ready_ring idle_ready_disjoint
             run_idle_disjoint])
  have wake_frame:
    "h_val (p2_wake_key_heap ?hr D) ?idle = h_val ?hr ?idle"
    by (rule p2_wake_key_heap_idle_item_frame[OF footprint])
  have remove_wake_frame: "h_val ?hk ?idle = h_val ?h ?idle"
    using remove_frame wake_frame
    by (simp only: p2_remove_then_wake_heap_def)
  have idle_delayed_disjoint:
    "raw_item_region ?idle \<inter> raw_list_region ?delayed = {}"
    by (rule p2_source_footprint_generic_item_root_disjointD[
          OF footprint _ delayed_root]) simp
  have insert_frame:
    "h_val
       (raw_ordered_insert_empty_heap ?hk ?delayed ?run) ?idle =
     h_val ?hk ?idle"
    by (rule raw_ordered_insert_empty_heap_preserves_disjoint_item[
          OF idle_delayed_disjoint run_idle_disjoint])
  show ?thesis
    using insert_frame remove_wake_frame
    by (simp only: p2_remove_wake_insert_heap_def)
qed

lemma p2_remove_wake_insert_ready0_refines:
  fixes c :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R c p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
  shows
    "sched_xlist_rel (sd_node_decode D)
       (p2_remove_wake_insert_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) D R)
       (abi_list_ptr (sr_ready R 0)) (sa_ready p2_post 0)"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?hf = "p2_remove_wake_insert_heap ?h D R"
  let ?ready0 = "abi_list_ptr (sr_ready R 0)"
  let ?idle = "abi_generic_list_item_ptr (sd_tcb_ptr D P2_IDLE)"
  have sched0:
    "sched_xlist_rel (sd_node_decode D) ?h ?ready0
       (sa_ready p2_pre 0)"
  proof -
    from lists have ready_all:
      "\<forall>p<4. sched_xlist_rel (sd_node_decode D) ?h
         (abi_list_ptr (sr_ready R p)) (sa_ready p2_pre p)"
      unfolding scheduler_lists_rel_def Let_def by blast
    show ?thesis by (rule ready_all[rule_format]) simp
  qed
  from sched0 obtain rx where
      raw: "raw_xlist_rel ?h ?ready0 rx"
    and relabel:
      "xlist_relabel (sd_node_decode D) rx (sa_ready p2_pre 0)"
    by (auto simp: sched_xlist_rel_def)
  have abs_ring:
    "ring (sa_ready p2_pre 0) = [Generic P2_IDLE]"
    by (simp add: p2_pre_def)
  have raw_length: "length (ring rx) = 1"
    using xlist_relabel_ring_length[OF relabel] abs_ring by simp
  then obtain p where raw_ring0: "ring rx = [p]"
    by (cases "ring rx") auto
  have pairs:
    "list_all2
       (\<lambda>q n. sd_node_decode D q = Some n)
       (ring rx) (ring (sa_ready p2_pre 0))"
    using relabel by (simp add: xlist_relabel_def)
  have p_decode: "sd_node_decode D p = Some (Generic P2_IDLE)"
    using pairs raw_ring0 abs_ring by simp
  have p_eq: "p = ?idle"
    using scheduler_node_decode_Generic_iff[
        OF decode, of p P2_IDLE] p_decode
    by (simp add: p2_pre_def)
  have raw_ring: "ring rx = [?idle]"
    using raw_ring0 p_eq by simp
  have physical_distinct: "distinct (p2_physical_roots R)"
    using footprint unfolding p2_source_footprint_def by blast
  have r0_r2: "sr_ready R 0 \<noteq> sr_ready R 2"
    using physical_distinct by (simp add: p2_physical_roots_def)
  have r2_r0: "sr_ready R 2 \<noteq> sr_ready R 0"
    by (rule p2_neq_sym[OF r0_r2])
  have r0_da: "sr_ready R 0 \<noteq> sr_delayed_a R"
    using physical_distinct by (simp add: p2_physical_roots_def)
  have da_r0: "sr_delayed_a R \<noteq> sr_ready R 0"
    by (rule p2_neq_sym[OF r0_da])
  have ready0_root:
    "sr_ready R 0 \<in> set (p2_physical_roots R)"
    by (simp add: p2_physical_roots_def)
  have list_frame: "h_val ?hf ?ready0 = h_val ?h ?ready0"
    by (rule p2_remove_wake_insert_other_root_frame[
          OF decode lists footprint ready0_root r2_r0 da_r0])
  have item_frame: "h_val ?hf ?idle = h_val ?h ?idle"
    by (rule p2_remove_wake_insert_idle_item_frame[
          OF decode lists footprint])
  have raw_final: "raw_xlist_rel ?hf ?ready0 rx"
    by (rule raw_xlist_rel_singleton_h_val_cong[
          OF raw raw_ring list_frame item_frame])
  have abstract_same:
    "sa_ready p2_post 0 = sa_ready p2_pre 0"
    by (simp add: p2_post_def p2_pre_def)
  show ?thesis
    using raw_final relabel abstract_same
    by (auto simp: sched_xlist_rel_def)
qed

lemma p2_remove_wake_insert_ready2_refines:
  fixes c :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R c p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
  shows
    "sched_xlist_rel (sd_node_decode D)
       (p2_remove_wake_insert_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) D R)
       (abi_list_ptr (sr_ready R 2)) (sa_ready p2_post 2)"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?ready = "abi_list_ptr (sr_ready R 2)"
  let ?delayed = "abi_list_ptr (sr_delayed_a R)"
  let ?p = "abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)"
  let ?hr = "raw_remove_concrete_heap ?h ?p"
  let ?hk = "p2_remove_then_wake_heap ?h D"
  have removed:
    "sched_xlist_rel (sd_node_decode D) ?hr ?ready
       (sa_ready p2_post 2)"
    by (rule p2_remove_ready2_refines_empty[OF decode lists])
  have ready_root: "sr_ready R 2 \<in> set (p2_physical_roots R)"
    by (simp add: p2_physical_roots_def)
  have delayed_root:
    "sr_delayed_a R \<in> set (p2_physical_roots R)"
    by (simp add: p2_physical_roots_def)
  have physical_distinct: "distinct (p2_physical_roots R)"
    using footprint unfolding p2_source_footprint_def by blast
  have ready_delayed_distinct: "sr_ready R 2 \<noteq> sr_delayed_a R"
    using physical_distinct by (simp add: p2_physical_roots_def)
  have roots_distinct: "sr_delayed_a R \<noteq> sr_ready R 2"
  proof
    assume equal: "sr_delayed_a R = sr_ready R 2"
    have "sr_ready R 2 = sr_delayed_a R"
      by (rule sym[OF equal])
    with ready_delayed_distinct show False by contradiction
  qed
  have roots_disjoint:
    "raw_list_region ?delayed \<inter> raw_list_region ?ready = {}"
    by (rule p2_source_footprint_raw_roots_disjointD[
          OF footprint delayed_root ready_root roots_distinct])
  have item_ready_disjoint:
    "raw_item_region ?p \<inter> raw_list_region ?ready = {}"
    by (rule p2_source_footprint_generic_item_root_disjointD[
          OF footprint _ ready_root]) simp
  have wake_frame:
    "h_val (p2_wake_key_heap ?hr D) ?ready = h_val ?hr ?ready"
    by (rule p2_wake_key_heap_raw_root_frame[OF footprint ready_root])
  have insert_frame:
    "h_val
       (raw_ordered_insert_empty_heap ?hk ?delayed ?p) ?ready =
     h_val ?hk ?ready"
    by (rule raw_ordered_insert_empty_heap_preserves_disjoint_list[
          OF roots_disjoint item_ready_disjoint])
  have final_frame:
    "h_val (p2_remove_wake_insert_heap ?h D R) ?ready =
     h_val ?hr ?ready"
    using wake_frame insert_frame
    by (simp only: p2_remove_then_wake_heap_def
        p2_remove_wake_insert_heap_def)
  have abs_ring: "ring (sa_ready p2_post 2) = []"
    by (simp add: p2_post_def empty_node_ring_def)
  have abs_cursor: "cursor (sa_ready p2_post 2) = None"
    by (simp add: p2_post_def empty_node_ring_def)
  show ?thesis
    by (rule sched_xlist_rel_empty_h_val_cong[
          OF removed abs_ring abs_cursor final_frame])
qed

theorem p2_remove_wake_insert_lists_rel:
  fixes c c' :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R c p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
    and heap:
      "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c') =
       p2_remove_wake_insert_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) D R"
  shows "scheduler_lists_rel D R c' p2_post"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?hf = "p2_remove_wake_insert_heap ?h D R"
  have ready0:
    "sched_xlist_rel (sd_node_decode D) ?hf
       (abi_list_ptr (sr_ready R 0)) (sa_ready p2_post 0)"
    by (rule p2_remove_wake_insert_ready0_refines[
          OF decode lists footprint])
  have ready2:
    "sched_xlist_rel (sd_node_decode D) ?hf
       (abi_list_ptr (sr_ready R 2)) (sa_ready p2_post 2)"
    by (rule p2_remove_wake_insert_ready2_refines[
          OF decode lists footprint])
  note empties = p2_remove_wake_insert_empty_components[
    OF decode lists footprint]
  from empties have ready1:
    "sched_xlist_rel (sd_node_decode D) ?hf
       (abi_list_ptr (sr_ready R 1)) (sa_ready p2_post 1)"
    by blast
  from empties have ready3:
    "sched_xlist_rel (sd_node_decode D) ?hf
       (abi_list_ptr (sr_ready R 3)) (sa_ready p2_post 3)"
    by blast
  from empties have delayed_b:
    "sched_xlist_rel (sd_node_decode D) ?hf
       (abi_list_ptr (sr_delayed_b R)) (sa_delayed_b p2_post)"
    by blast
  from empties have pending:
    "sched_xlist_rel (sd_node_decode D) ?hf
       (abi_list_ptr (sr_pending R)) (sa_pending p2_post)"
    by blast
  from empties have suspended:
    "sched_xlist_rel (sd_node_decode D) ?hf
       (abi_list_ptr (sr_suspended R)) (sa_suspended p2_post)"
    by blast
  have delayed_a:
    "sched_xlist_rel (sd_node_decode D) ?hf
       (abi_list_ptr (sr_delayed_a R)) (sa_delayed_a p2_post)"
    by (rule p2_remove_wake_insert_delayed_a_final[
          OF decode lists footprint])
  have ready_all:
    "\<forall>p<4. sched_xlist_rel (sd_node_decode D) ?hf
       (abi_list_ptr (sr_ready R p)) (sa_ready p2_post p)"
  proof (intro allI impI)
    fix p :: nat
    assume less: "p < 4"
    have cases: "p = 0 \<or> p = 1 \<or> p = 2 \<or> p = 3"
      using less by arith
    show
      "sched_xlist_rel (sd_node_decode D) ?hf
        (abi_list_ptr (sr_ready R p)) (sa_ready p2_post p)"
      using cases ready0 ready1 ready2 ready3 by auto
  qed
  show ?thesis
    unfolding scheduler_lists_rel_def Let_def
    apply (simp only: heap)
    using ready_all delayed_a delayed_b pending suspended by blast
qed

end
