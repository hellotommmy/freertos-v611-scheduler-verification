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

end
