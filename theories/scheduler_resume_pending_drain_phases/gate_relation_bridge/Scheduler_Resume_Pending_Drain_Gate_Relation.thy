theory Scheduler_Resume_Pending_Drain_Gate_Relation
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage.Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage"
begin

theorem resume_pending_gate_head_owner_priorityD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "scheduler_list_head_item
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (sr_pending R) =
         scheduler_event_item_ptr (sd_tcb_ptr D t) \<and>
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (scheduler_list_head_item
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
           (sr_pending R))) =
       PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
         (sd_tcb_ptr D t) \<and>
     unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (sd_tcb_ptr D t))) = rpc_priority C t \<and>
     rpc_priority C t < 4"
proof -
  have root: "rpc_pending_root C \<in> rpc_event_roots C"
    using resume_pending_gate_pure_entryD[OF rel]
    by (auto simp: resume_pending_entry_rel_def resume_pending_context_wf_def)
  have lists:
    "sched_xlist_rel (sd_node_decode D)
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (rpc_pending_root C)
       (rps_event_family S (rpc_pending_root C))"
    by (rule scheduler_event_root_family_sched_xlistD[
      OF resume_pending_gate_event_familyD[OF rel] root])
  have root_eq:
    "rpc_pending_root C = abi_list_ptr (sr_pending R)"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def
    by blast
  have lists_source:
    "sched_xlist_rel (sd_node_decode D)
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (abi_list_ptr (sr_pending R))
       (rps_event_family S (rpc_pending_root C))"
    using lists root_eq by simp
  have head:
    "ring (rps_event_family S (rpc_pending_root C)) =
       Event t # map Event rest"
    using resume_pending_gate_pure_entryD[OF rel] tasks
    by (simp add: resume_pending_entry_rel_def)
  note observed = represented_event_head_owner_priority[
    OF lists_source resume_pending_gate_decoderD[OF rel]
      resume_pending_gate_task_observationD[OF rel] head]
  have head_ptr:
    "scheduler_list_head_item
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (sr_pending R) = scheduler_event_item_ptr (sd_tcb_ptr D t)"
    using observed by blast
  have owner:
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (scheduler_list_head_item
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
           (sr_pending R))) =
       PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
         (sd_tcb_ptr D t)"
    using observed by blast
  have observed_priority:
    "unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (sd_tcb_ptr D t))) = sa_priority a t"
    using observed by blast
  have observed_bound: "sa_priority a t < 4"
    using observed by blast
  have priority: "rpc_priority C t = sa_priority a t"
    using rel resume_pending_gate_head_liveD[OF rel tasks]
    unfolding resume_pending_gate_entry_rel_def Let_def
    by blast
  have context_priority:
    "unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (sd_tcb_ptr D t))) = rpc_priority C t"
    using observed_priority priority by simp
  have context_bound: "rpc_priority C t < 4"
    using observed_bound priority by simp
  show ?thesis
  proof (intro conjI)
    show "scheduler_list_head_item
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
        (sr_pending R) = scheduler_event_item_ptr (sd_tcb_ptr D t)"
      by (rule head_ptr)
    show "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
        (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
          (scheduler_list_head_item
            (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
            (sr_pending R))) =
          PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
            (sd_tcb_ptr D t)"
      by (rule owner)
    show "unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
        (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
          (sd_tcb_ptr D t))) = rpc_priority C t"
      by (rule context_priority)
    show "rpc_priority C t < 4"
      by (rule context_bound)
  qed
qed

corollary resume_pending_gate_source_pending_rootD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
  shows
    "rpc_pending_root C =
       abi_list_ptr Scheduler_V611_Parse.xPendingReadyList_'"
  using rel roots
  unfolding resume_pending_gate_entry_rel_def Let_def
  by simp

corollary resume_pending_gate_source_pending_guardD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
  shows "c_guard Scheduler_V611_Parse.xPendingReadyList_'"
proof -
  have root: "rpc_pending_root C \<in> rpc_event_roots C"
    using resume_pending_gate_pure_entryD[OF rel]
    by (auto simp: resume_pending_entry_rel_def resume_pending_context_wf_def)
  have raw:
    "raw_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (rpc_pending_root C) (event_raw (rpc_pending_root C))"
    by (rule scheduler_event_root_family_raw_rootD[
      OF resume_pending_gate_event_familyD[OF rel] root])
  have raw_guard: "c_guard (rpc_pending_root C)"
    using raw
    by (simp add: raw_xlist_rel_def raw_xlist_layout_def)
  have source:
    "rpc_pending_root C =
       abi_list_ptr Scheduler_V611_Parse.xPendingReadyList_'"
    by (rule resume_pending_gate_source_pending_rootD[OF rel roots])
  have "c_guard
      (abi_list_ptr Scheduler_V611_Parse.xPendingReadyList_')"
    using raw_guard source by simp
  then show ?thesis by (simp only: abi_list_ptr_c_guard)
qed

corollary resume_pending_gate_source_ready_rootD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
    and live: "t \<in> rpc_live C"
  shows
    "rpc_ready_root C (rpc_priority C t) =
       abi_list_ptr
         (array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_'
           False (rpc_priority C t))"
proof -
  have ready:
    "rpc_ready_root C (rpc_priority C t) =
       abi_list_ptr (sr_ready R (rpc_priority C t))"
    using rel live
    unfolding resume_pending_gate_entry_rel_def Let_def
    by blast
  show ?thesis using ready roots by simp
qed

end
