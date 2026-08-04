theory Scheduler_One_Due_Task_Phases_Delayed_Head
  imports
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Tail_Insert.Scheduler_One_Due_Task_Phases_Tail_Insert"
    "EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Preservation.Scheduler_Family_Insert_End_Preservation"
begin

text \<open>
  The whole Generic family survives the ready insertion.  The after-event
  family -- the delayed source shrunk by the due task, every other root
  unchanged -- satisfies the packaged family relation at the after-event
  heap, the due task's Generic item is globally unlinked there, and the
  accepted insert-end preservation theorem then delivers the family
  relation at the exact insert heap: the ready target gains the item at
  the end, and in particular the shrunk delayed source ring is exactly
  what the generated delayed-head re-read visits.  No ring population,
  priority or heap layout is fixed.
\<close>

lemma one_due_after_remove_ring_subset:
  "set (ring (one_due_generic_raw_after_remove D C fam lp)) \<subseteq>
     set (ring (fam lp))"
  by (auto simp: one_due_generic_raw_after_remove_def
      list_remove_abs_def dest!: subsetD[OF set_remove1_subset])

lemma one_due_after_event_pre_rel:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "scheduler_family_pre_rel
       (one_due_event_remove_heap D C branch
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
       (odc_generic_roots C)
       (one_due_generic_raw_after_remove D C generic_raw)
       (odc_live C) D"
proof -
  let ?he = "one_due_event_remove_heap D C branch
    (one_due_generic_remove_heap D C
      (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))"
  let ?fam = "one_due_generic_raw_after_remove D C generic_raw"
  let ?source = "odc_delayed_root C"
  note pre = one_due_gateH_generic_preD[OF rel]
  note after_event = one_due_gateH_after_event_obligations[OF rel]
  have family:
    "raw_family_rel ?he (odc_generic_roots C) ?fam"
    unfolding raw_family_rel_def
  proof (intro conjI ballI)
    show "finite (odc_generic_roots C)"
      using pre
      by (simp add: scheduler_family_pre_rel_def raw_family_rel_def)
  next
    fix g
    assume g_root: "g \<in> odc_generic_roots C"
    show "raw_xlist_rel ?he g (?fam g)"
    proof (cases "g = ?source")
      case True
      show ?thesis
        using after_event True
        by (simp add: one_due_after_event_obligations_def Let_def
            one_due_generic_raw_after_remove_def)
    next
      case False
      show ?thesis
        using after_event g_root False
        by (simp add: one_due_after_event_obligations_def Let_def
            one_due_generic_raw_after_remove_def)
    qed
  qed
  have managed:
    "\<forall>lp\<in>odc_generic_roots C.
       set (ring (?fam lp)) \<subseteq>
         universal_managed_nodes (odc_live C) D"
  proof (intro ballI)
    fix lp
    assume lp_root: "lp \<in> odc_generic_roots C"
    have base:
      "set (ring (generic_raw lp)) \<subseteq>
         universal_managed_nodes (odc_live C) D"
      using pre lp_root
      by (auto simp: scheduler_family_pre_rel_def
          one_due_generic_raw_set_def universal_managed_nodes_def
          one_due_generic_raw_ptr_def)
    show "set (ring (?fam lp)) \<subseteq>
       universal_managed_nodes (odc_live C) D"
      using one_due_after_remove_ring_subset[of D C generic_raw lp] base
      by blast
  qed
  have rings:
    "\<forall>lp\<in>odc_generic_roots C. \<forall>lq\<in>odc_generic_roots C.
       lp \<noteq> lq \<longrightarrow>
       set (ring (?fam lp)) \<inter> set (ring (?fam lq)) = {}"
  proof (intro ballI impI)
    fix lp lq
    assume roots_in: "lp \<in> odc_generic_roots C"
      "lq \<in> odc_generic_roots C" and ne: "lp \<noteq> lq"
    have base:
      "set (ring (generic_raw lp)) \<inter>
         set (ring (generic_raw lq)) = {}"
      using pre roots_in ne
      by (auto simp: scheduler_family_pre_rel_def)
    show "set (ring (?fam lp)) \<inter> set (ring (?fam lq)) = {}"
      using one_due_after_remove_ring_subset[of D C generic_raw lp]
        one_due_after_remove_ring_subset[of D C generic_raw lq] base
      by blast
  qed
  show ?thesis
    using pre family managed rings
    by (simp add: scheduler_family_pre_rel_def)
qed

lemma one_due_absent_after_removal:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "raw_family_members (odc_generic_roots C)
       (one_due_generic_raw_after_remove D C generic_raw)
       (one_due_generic_raw_ptr D (odc_task C)) = {}"
proof -
  let ?source = "odc_delayed_root C"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  have owner:
    "scheduler_delay_owner_entry_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (odc_generic_roots C) generic_raw ?source ?p"
    using rel
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have members:
    "raw_family_members (odc_generic_roots C) generic_raw ?p =
       {?source}"
    using owner
    by (simp add: scheduler_delay_owner_entry_rel_def)
  have source_root: "?source \<in> odc_generic_roots C"
    by (rule one_due_gateH_source_in_rootsD[OF rel])
  have source_rel:
    "raw_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       ?source (generic_raw ?source)"
    using one_due_gateH_generic_preD[OF rel] source_root
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have dist: "distinct (ring (generic_raw ?source))"
    using source_rel
    by (simp add: raw_xlist_rel_def raw_xlist_view_def xlist_wf_def)
  have not_in_removed:
    "?p \<notin> set (ring (one_due_generic_raw_after_remove D C
        generic_raw ?source))"
    using dist
    by (simp add: one_due_generic_raw_after_remove_def
        list_remove_abs_def)
  show ?thesis
  proof (rule equals0I)
    fix g
    assume g_in:
      "g \<in> raw_family_members (odc_generic_roots C)
        (one_due_generic_raw_after_remove D C generic_raw) ?p"
    have g_root: "g \<in> odc_generic_roots C"
      and g_member:
        "?p \<in> set (ring (one_due_generic_raw_after_remove D C
           generic_raw g))"
      using g_in by (auto simp: raw_family_members_def)
    show False
    proof (cases "g = ?source")
      case True
      then show False
        using g_member not_in_removed by simp
    next
      case False
      have "?p \<in> set (ring (generic_raw g))"
        using g_member False
        by (simp add: one_due_generic_raw_after_remove_def)
      then have "g \<in> raw_family_members (odc_generic_roots C)
          generic_raw ?p"
        using g_root by (simp add: raw_family_members_def)
      then show False
        using members False by simp
    qed
  qed
qed

theorem one_due_insert_family_pre_rel:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "scheduler_family_pre_rel
       (one_due_ready_insert_heap D C generic_raw
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
       (odc_generic_roots C)
       (scheduler_family_insert_end_raw
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
         (one_due_generic_raw_after_remove D C generic_raw)
         (one_due_target_root C)
         (one_due_generic_raw_ptr D (odc_task C)))
       (odc_live C) D"
proof -
  let ?he = "one_due_event_remove_heap D C branch
    (one_due_generic_remove_heap D C
      (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))"
  let ?fam = "one_due_generic_raw_after_remove D C generic_raw"
  let ?target = "one_due_target_root C"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  have task_live: "odc_task C \<in> odc_live C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have target_ne: "?target \<noteq> odc_delayed_root C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have fam_target: "?fam ?target = generic_raw ?target"
    using target_ne
    by (simp add: one_due_generic_raw_after_remove_def)
  note after_event = one_due_gateH_after_event_obligations[OF rel]
  have fresh:
    "raw_fresh_for_insert ?target (ring (?fam ?target)) ?p"
    using after_event fam_target
    by (simp add: one_due_after_event_obligations_def Let_def)
  have managed: "?p \<in> universal_managed_nodes (odc_live C) D"
    using task_live
    by (auto simp: universal_managed_nodes_def
        one_due_generic_raw_ptr_def)
  have heap_eq:
    "raw_insert_concrete_heap ?he ?target (?fam ?target) ?p =
     one_due_ready_insert_heap D C generic_raw ?he"
    using fam_target
    by (simp add: one_due_ready_insert_heap_def)
  note result = scheduler_family_insert_end_pre_rel_and_linked[
    OF one_due_after_event_pre_rel[OF rel]
      one_due_gateH_target_in_rootsD[OF rel] fresh managed
      one_due_absent_after_removal[OF rel]]
  show ?thesis
    using result heap_eq by simp
qed

corollary one_due_source_rel_at_insert:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "raw_xlist_rel
       (one_due_ready_insert_heap D C generic_raw
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
       (odc_delayed_root C)
       (list_remove_abs (one_due_generic_raw_ptr D (odc_task C))
         (generic_raw (odc_delayed_root C)))"
proof -
  have target_ne: "one_due_target_root C \<noteq> odc_delayed_root C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have source_root: "odc_delayed_root C \<in> odc_generic_roots C"
    by (rule one_due_gateH_source_in_rootsD[OF rel])
  show ?thesis
    using one_due_insert_family_pre_rel[OF rel] source_root target_ne
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def
        scheduler_family_insert_end_raw_def
        one_due_generic_raw_after_remove_def)
qed

lemma raw_ring_links_end_next:
  assumes links: "raw_ring_links h lp rs"
  shows
    "List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxNext_C
       (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
         (h_val h lp)) =
     (if rs = [] then raw_end_item lp else hd rs)"
  using links
  by (cases rs)
     (auto simp: raw_ring_links_def raw_edge_pairs_def raw_next_at_def)

lemma one_due_gateH_delayed_root_globalD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "odc_delayed_root C =
       abi_list_ptr (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)"
  using rel
  unfolding one_due_gateH_entry_rel_def Let_def
  by blast

lemma one_due_delayed_count_at_insert:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "unat (Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
       (h_val
         (one_due_ready_insert_heap D C generic_raw
           (one_due_event_remove_heap D C branch
             (one_due_generic_remove_heap D C
               (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
         (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c))) =
     length (ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C))))"
proof -
  have raw_count:
    "unat (List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
       (h_val
         (one_due_ready_insert_heap D C generic_raw
           (one_due_event_remove_heap D C branch
             (one_due_generic_remove_heap D C
               (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
         (odc_delayed_root C))) =
     length (ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C))))"
    using one_due_source_rel_at_insert[OF rel]
    by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  show ?thesis
    using raw_count one_due_gateH_delayed_root_globalD[OF rel]
    by (simp add: abi_list_count_h_val)
qed

lemma one_due_delayed_end_next_at_insert:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "abi_item_ptr
       (Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxNext_C
         (Scheduler_V611_Parse.xLIST_C.xListEnd_C
           (h_val
             (one_due_ready_insert_heap D C generic_raw
               (one_due_event_remove_heap D C branch
                 (one_due_generic_remove_heap D C
                   (hrs_mem
                     (Scheduler_V611_Parse.globals.t_hrs_' c)))))
             (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)))) =
     (if ring (list_remove_abs
          (one_due_generic_raw_ptr D (odc_task C))
          (generic_raw (odc_delayed_root C))) = []
      then raw_end_item (odc_delayed_root C)
      else hd (ring (list_remove_abs
          (one_due_generic_raw_ptr D (odc_task C))
          (generic_raw (odc_delayed_root C)))))"
proof -
  have links:
    "raw_ring_links
       (one_due_ready_insert_heap D C generic_raw
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
       (odc_delayed_root C)
       (ring (list_remove_abs
         (one_due_generic_raw_ptr D (odc_task C))
         (generic_raw (odc_delayed_root C))))"
    using one_due_source_rel_at_insert[OF rel]
    by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  show ?thesis
    using raw_ring_links_end_next[OF links]
      one_due_gateH_delayed_root_globalD[OF rel]
    by (simp add: abi_sentinel_next_h_val)
qed

end
