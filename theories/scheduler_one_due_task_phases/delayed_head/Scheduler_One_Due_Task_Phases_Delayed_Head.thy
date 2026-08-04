theory Scheduler_One_Due_Task_Phases_Delayed_Head
  imports
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Tail_Insert.Scheduler_One_Due_Task_Phases_Tail_Insert"
    "EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Preservation.Scheduler_Family_Insert_End_Preservation"
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Owner_Frame.Scheduler_Resume_Generated_Owner_Frame"
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

lemma scheduler_family_pre_rel_storage_disjoint:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and lp_root: "lp \<in> roots"
    and lq_root: "lq \<in> roots"
    and ne: "lp \<noteq> lq"
  shows
    "raw_xlist_storage lp (fam lp) \<inter>
       raw_xlist_storage lq (fam lq) = {}"
proof -
  have geometry: "universal_tcb_geometry live D"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have managed_p:
    "set (ring (fam lp)) \<subseteq> universal_managed_nodes live D"
    and managed_q:
    "set (ring (fam lq)) \<subseteq> universal_managed_nodes live D"
    using pre lp_root lq_root
    by (auto simp: scheduler_family_pre_rel_def)
  have roots_disj: "raw_list_region lp \<inter> raw_list_region lq = {}"
    using pre lp_root lq_root ne
    by (auto simp: scheduler_family_pre_rel_def)
  have rings_disj:
    "set (ring (fam lp)) \<inter> set (ring (fam lq)) = {}"
    using pre lp_root lq_root ne
    by (auto simp: scheduler_family_pre_rel_def)
  have root_item_p:
    "\<And>q. q \<in> set (ring (fam lq)) \<Longrightarrow>
       raw_list_region lp \<inter> raw_item_region q = {}"
  proof -
    fix q assume "q \<in> set (ring (fam lq))"
    then have "q \<in> universal_managed_nodes live D"
      using managed_q by blast
    then show "raw_list_region lp \<inter> raw_item_region q = {}"
      by (rule scheduler_family_root_managed_item_disjoint[
        OF pre lp_root])
  qed
  have root_item_q:
    "\<And>p. p \<in> set (ring (fam lp)) \<Longrightarrow>
       raw_list_region lq \<inter> raw_item_region p = {}"
  proof -
    fix p assume "p \<in> set (ring (fam lp))"
    then have "p \<in> universal_managed_nodes live D"
      using managed_p by blast
    then show "raw_list_region lq \<inter> raw_item_region p = {}"
      by (rule scheduler_family_root_managed_item_disjoint[
        OF pre lq_root])
  qed
  have items:
    "\<And>p q. p \<in> set (ring (fam lp)) \<Longrightarrow>
       q \<in> set (ring (fam lq)) \<Longrightarrow>
       raw_item_region p \<inter> raw_item_region q = {}"
  proof -
    fix p q
    assume p_in: "p \<in> set (ring (fam lp))"
      and q_in: "q \<in> set (ring (fam lq))"
    have p_managed: "p \<in> universal_managed_nodes live D"
      using managed_p p_in by blast
    have q_managed: "q \<in> universal_managed_nodes live D"
      using managed_q q_in by blast
    have distinct: "p \<noteq> q"
      using p_in q_in rings_disj by blast
    show "raw_item_region p \<inter> raw_item_region q = {}"
      by (rule universal_distinct_managed_item_regions_disjoint[
        OF geometry p_managed q_managed distinct])
  qed
  show ?thesis
    using roots_disj root_item_p root_item_q items
    by (fastforce simp: raw_xlist_storage_def)
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

lemma one_due_delayed_head_guard_at_insert:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and nonempty:
      "ring (list_remove_abs
         (one_due_generic_raw_ptr D (odc_task C))
         (generic_raw (odc_delayed_root C))) \<noteq> []"
  shows
    "c_guard (hd (ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C)))))"
proof -
  have layout:
    "raw_xlist_layout (odc_delayed_root C)
       (ring (list_remove_abs
         (one_due_generic_raw_ptr D (odc_task C))
         (generic_raw (odc_delayed_root C))))"
    using one_due_source_rel_at_insert[OF rel]
    by (simp add: raw_xlist_rel_def)
  have hd_in:
    "hd (ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C)))) \<in>
     set (ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C))))"
    using nonempty by (rule hd_in_set)
  show ?thesis
    using layout hd_in
    by (auto simp: raw_xlist_layout_def)
qed

lemma one_due_source_member_owner_bytes_at_insert:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and q_member:
      "q \<in> set (ring (generic_raw (odc_delayed_root C)))"
    and q_ne: "q \<noteq> one_due_generic_raw_ptr D (odc_task C)"
  shows
    "\<forall>addr\<in>raw_owner_field_region q.
       one_due_ready_insert_heap D C generic_raw
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
         addr =
       hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c) addr"
proof (intro ballI)
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?hg = "one_due_generic_remove_heap D C ?h"
  let ?he = "one_due_event_remove_heap D C branch ?hg"
  let ?hi = "one_due_ready_insert_heap D C generic_raw ?he"
  let ?source = "odc_delayed_root C"
  let ?target = "one_due_target_root C"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  fix addr
  assume addr: "addr \<in> raw_owner_field_region q"
  have addr_item: "addr \<in> raw_item_region q"
    using addr raw_owner_field_region_subset_item by blast
  have source_root: "?source \<in> odc_generic_roots C"
    by (rule one_due_gateH_source_in_rootsD[OF rel])
  have source_rel_h:
    "raw_xlist_rel ?h ?source (generic_raw ?source)"
    using one_due_gateH_generic_preD[OF rel] source_root
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have p_member: "?p \<in> set (ring (generic_raw ?source))"
    by (rule one_due_gateH_source_memberD[OF rel])
  have step1: "?hg addr = ?h addr"
    unfolding one_due_generic_remove_heap_def
    using raw_remove_member_owner_byte_frame[OF source_rel_h p_member
      q_member] addr
    by blast
  have q_in_source_storage:
    "addr \<in> raw_xlist_storage ?source (generic_raw ?source)"
    using addr_item q_member
    by (auto simp: raw_xlist_storage_def)
  have step2: "?he addr = ?hg addr"
  proof (cases branch)
    case DueEventNull
    then show ?thesis
      by (simp add: one_due_event_remove_heap_def)
  next
    case (DueEventLinked owner)
    have rel_linked:
      "one_due_gateH_entry_rel D R c a C (DueEventLinked owner) S
         generic_raw event_raw"
      using rel DueEventLinked by simp
    have owner_facts:
      "raw_xlist_rel ?hg owner (event_raw owner) \<and>
       event_item_raw_ptr D (odc_task C) \<in>
         set (ring (event_raw owner))"
      by (rule one_due_gateH_linked_event_after_genericD[OF rel_linked])
    have owner_root: "owner \<in> odc_event_roots C"
      by (rule one_due_gateH_linked_ownerD[OF rel_linked])
    have footprint:
      "raw_remove_exact_write_footprint ?hg owner
         (event_item_raw_ptr D (odc_task C)) \<subseteq>
       raw_xlist_storage owner (event_raw owner)"
      using owner_facts
      by (intro raw_remove_exact_footprint_subset_storage) blast+
    have disj:
      "raw_xlist_storage ?source (generic_raw ?source) \<inter>
         raw_xlist_storage owner (event_raw owner) = {}"
      by (rule one_due_gateH_storage_disjointD[OF rel source_root
        owner_root])
    have outside:
      "addr \<notin> raw_remove_exact_write_footprint ?hg owner
         (event_item_raw_ptr D (odc_task C))"
      using footprint disj q_in_source_storage by blast
    show ?thesis
      using owner_facts DueEventLinked
      by (auto simp: one_due_event_remove_heap_def
          intro: raw_remove_concrete_heap_exact_external_frame[
            OF _ _ outside])
  qed
  have target_root: "?target \<in> odc_generic_roots C"
    by (rule one_due_gateH_target_in_rootsD[OF rel])
  have target_ne: "?target \<noteq> ?source"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  note after_pre = one_due_after_event_pre_rel[OF rel]
  have fam_he_target:
    "one_due_generic_raw_after_remove D C generic_raw ?target =
       generic_raw ?target"
    using target_ne
    by (simp add: one_due_generic_raw_after_remove_def)
  have target_rel_he:
    "raw_xlist_rel ?he ?target (generic_raw ?target)"
    using after_pre target_root fam_he_target
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  note after_event = one_due_gateH_after_event_obligations[OF rel]
  have fresh:
    "raw_fresh_for_insert ?target (ring (generic_raw ?target)) ?p"
    using after_event
    by (simp add: one_due_after_event_obligations_def Let_def)
  have q_in_removed:
    "q \<in> set (ring (one_due_generic_raw_after_remove D C
       generic_raw ?source))"
    using q_member q_ne
    by (simp add: one_due_generic_raw_after_remove_def
        list_remove_abs_def)
  have storage_disj:
    "raw_xlist_storage ?source
       (one_due_generic_raw_after_remove D C generic_raw ?source) \<inter>
     raw_xlist_storage ?target
       (one_due_generic_raw_after_remove D C generic_raw ?target) = {}"
    by (rule scheduler_family_pre_rel_storage_disjoint[OF after_pre
      source_root target_root target_ne[symmetric]])
  have addr_in_removed_storage:
    "addr \<in> raw_xlist_storage ?source
       (one_due_generic_raw_after_remove D C generic_raw ?source)"
    using addr_item q_in_removed
    by (auto simp: raw_xlist_storage_def)
  have footprint_i:
    "raw_insert_end_exact_write_footprint ?he ?target
       (generic_raw ?target) ?p \<subseteq>
     raw_xlist_storage ?target (generic_raw ?target) \<union>
       raw_item_region ?p"
    by (rule raw_insert_end_exact_footprint_subset_storage[
      OF target_rel_he])
  have task_live: "odc_task C \<in> odc_live C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have geometry: "universal_tcb_geometry (odc_live C) D"
    using one_due_gateH_generic_preD[OF rel]
    by (simp add: scheduler_family_pre_rel_def)
  have q_managed: "q \<in> universal_managed_nodes (odc_live C) D"
    using one_due_gateH_generic_preD[OF rel] source_root q_member
    by (auto simp: scheduler_family_pre_rel_def)
  have p_managed: "?p \<in> universal_managed_nodes (odc_live C) D"
    using task_live
    by (auto simp: universal_managed_nodes_def
        one_due_generic_raw_ptr_def)
  have qp_disj: "raw_item_region q \<inter> raw_item_region ?p = {}"
    by (rule universal_distinct_managed_item_regions_disjoint[
      OF geometry q_managed p_managed q_ne])
  have outside_i:
    "addr \<notin> raw_insert_end_exact_write_footprint ?he ?target
       (generic_raw ?target) ?p"
  proof
    assume inside:
      "addr \<in> raw_insert_end_exact_write_footprint ?he ?target
         (generic_raw ?target) ?p"
    have "addr \<in> raw_xlist_storage ?target (generic_raw ?target) \<or>
       addr \<in> raw_item_region ?p"
      using footprint_i inside by blast
    then show False
      using storage_disj addr_in_removed_storage fam_he_target
        qp_disj addr_item
      by auto
  qed
  have step3: "?hi addr = ?he addr"
    unfolding one_due_ready_insert_heap_def
    by (rule raw_insert_concrete_heap_exact_external_frame[
      OF target_rel_he fresh outside_i])
  show "?hi addr = ?h addr"
    using step1 step2 step3 by simp
qed

end
