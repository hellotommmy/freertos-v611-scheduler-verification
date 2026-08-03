theory Scheduler_Resume_Generated_Next_Head
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Insert_Event_Family.Scheduler_Resume_Generated_Insert_Event_Family"
begin

text \<open>
  The generated pending-ready drain body ends by re-reading the pending
  list's head.  This theory executes that generated read from the
  ready-inserted cutpoint state: with the drained head gone, the read
  returns exactly the next pending task's TCB when any remains, and NULL
  when the drained task was the last one.  The next head is whatever task
  the arbitrary pending context lists second; nothing about it is fixed.
\<close>

section \<open>Owner observation transported to the inserted heap\<close>

lemma resume_pending_event_owner_transport:
  assumes frame:
      "h_val h' (event_item_raw_ptr D u) =
       h_val h (event_item_raw_ptr D u)"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h' (scheduler_event_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D u)))"
  using frame
  by (simp add: event_item_raw_ptr_def abi_event_list_item_ptr_def
      scheduler_event_item_ptr_def flip: abi_item_owner_h_val)

lemma resume_pending_inserted_event_owner_observationD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and pending_u: "u \<in> set (rpc_tasks C)"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
         (scheduler_event_item_ptr (sd_tcb_ptr D u))) =
     PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
       (sd_tcb_ptr D u)"
proof -
  have live: "u \<in> rpc_live C"
    by (rule resume_pending_gate_pending_liveD[OF rel pending_u])
  have observation:
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a"
    by (rule resume_pending_gate_task_observationD[OF rel])
  have live_abs: "u \<in> sa_live a"
    using rel live
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  have entry_owner:
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (scheduler_event_item_ptr (sd_tcb_ptr D u))) =
     PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
       (sd_tcb_ptr D u)"
    using TaskObservationRel_liveD[OF observation live_abs] by blast
  note event_step =
    resume_pending_event_remove_owner_frame[OF rel tasks pending_u]
  note generic_step = resume_pending_event_owner_transport[
    OF resume_pending_generic_remove_event_item_frame[OF rel tasks live]]
  note insert_step = resume_pending_event_owner_transport[
    OF resume_pending_ready_insert_event_item_frame[OF rel tasks live]]
  show ?thesis
    using insert_step generic_step event_step entry_owner by simp
qed

section \<open>Pending count at the inserted heap\<close>

lemma resume_pending_inserted_pending_count:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and roots: "R = generated_scheduler_roots"
  shows
    "unat (Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
         Scheduler_V611_Parse.xPendingReadyList_')) = length rest"
proof -
  have pending_root: "rpc_pending_root C \<in> rpc_event_roots C"
    using resume_pending_gate_pure_entryD[OF rel]
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_context_wf_def)
  note family = resume_pending_ready_insert_event_family_frame[
    OF rel tasks]
  have count:
    "unat (List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
         (rpc_pending_root C))) =
       length (ring (rps_event_family
         (resume_pending_event_unlink_state C t S) (rpc_pending_root C)))"
    by (rule scheduler_event_root_family_countD[OF family pending_root])
  have entry_ring:
    "ring (rps_event_family S (rpc_pending_root C)) =
       Event t # map Event rest"
    using resume_pending_gate_pure_entryD[OF rel] tasks
    by (simp add: resume_pending_entry_rel_def)
  have after_ring:
    "ring (rps_event_family
       (resume_pending_event_unlink_state C t S) (rpc_pending_root C)) =
     map Event rest"
    using resume_pending_event_unlink_ring[of C t S] entry_ring by simp
  have root:
    "rpc_pending_root C =
       abi_list_ptr Scheduler_V611_Parse.xPendingReadyList_'"
    by (rule resume_pending_gate_source_pending_rootD[OF rel roots])
  show ?thesis
    using count after_ring root
    by (simp add: abi_list_count_h_val)
qed

section \<open>Exact generated next-head read: last pending task drained\<close>

theorem resume_pending_generated_head_read_drained_empty:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = [t]"
    and roots: "R = generated_scheduler_roots"
  shows
    "resume_pending_generated_head_read \<bullet>
       (resume_pending_ready_inserted_state D C t generic_raw c)
     \<lbrace>\<lambda>r s.
       r = Result NULL \<and>
       s = resume_pending_ready_inserted_state D C t generic_raw c
     \<rbrace>"
proof -
  have count:
    "unat (Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
         Scheduler_V611_Parse.xPendingReadyList_')) = 0"
    using resume_pending_inserted_pending_count[OF rel _ roots] tasks
    by simp
  have zero:
    "Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
         Scheduler_V611_Parse.xPendingReadyList_') = 0"
    using count by (simp add: unat_eq_0)
  show ?thesis
    unfolding resume_pending_generated_head_read_def
    apply runs_to_vcg
    using zero by simp_all
qed

section \<open>Exact generated next-head read: further pending tasks remain\<close>

theorem resume_pending_generated_head_read_drained_nonempty:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # t' # rest'"
    and roots: "R = generated_scheduler_roots"
  shows
    "resume_pending_generated_head_read \<bullet>
       (resume_pending_ready_inserted_state D C t generic_raw c)
     \<lbrace>\<lambda>r s.
       r = Result
         (PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
           (sd_tcb_ptr D t')) \<and>
       s = resume_pending_ready_inserted_state D C t generic_raw c
     \<rbrace>"
proof -
  let ?inserted = "resume_pending_ready_inserted_state D C t generic_raw c"
  let ?heap = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?inserted)"
  have tasks_cons: "rpc_tasks C = t # (t' # rest')"
    using tasks by simp
  have count_val:
    "unat (Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
       (h_val ?heap Scheduler_V611_Parse.xPendingReadyList_')) =
     length (t' # rest')"
    using resume_pending_inserted_pending_count[OF rel tasks_cons roots]
    by simp
  have count_nonzero:
    "Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
       (h_val ?heap Scheduler_V611_Parse.xPendingReadyList_') \<noteq> 0"
    using count_val by (auto simp: unat_eq_0)
  have pending_root: "rpc_pending_root C \<in> rpc_event_roots C"
    using resume_pending_gate_pure_entryD[OF rel]
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_context_wf_def)
  note family = resume_pending_ready_insert_event_family_frame[
    OF rel tasks_cons]
  have lists:
    "sched_xlist_rel (sd_node_decode D) ?heap (rpc_pending_root C)
       (rps_event_family (resume_pending_event_unlink_state C t S)
         (rpc_pending_root C))"
    by (rule scheduler_event_root_family_sched_xlistD[
      OF family pending_root])
  have root:
    "rpc_pending_root C =
       abi_list_ptr Scheduler_V611_Parse.xPendingReadyList_'"
    by (rule resume_pending_gate_source_pending_rootD[OF rel roots])
  have entry_ring:
    "ring (rps_event_family S (rpc_pending_root C)) =
       Event t # Event t' # map Event rest'"
    using resume_pending_gate_pure_entryD[OF rel] tasks
    by (simp add: resume_pending_entry_rel_def)
  have after_ring:
    "ring (rps_event_family
       (resume_pending_event_unlink_state C t S) (rpc_pending_root C)) =
     Event t' # map Event rest'"
    using resume_pending_event_unlink_ring[of C t S] entry_ring by simp
  have lists_source:
    "sched_xlist_rel (sd_node_decode D) ?heap
       (abi_list_ptr Scheduler_V611_Parse.xPendingReadyList_')
       (rps_event_family (resume_pending_event_unlink_state C t S)
         (rpc_pending_root C))"
    using lists root by simp
  have head_item:
    "scheduler_list_head_item ?heap
       Scheduler_V611_Parse.xPendingReadyList_' =
     scheduler_event_item_ptr (sd_tcb_ptr D t')"
    by (rule sched_xlist_rel_event_head_ptr[
      OF lists_source resume_pending_gate_decoderD[OF rel] after_ring])
  have head_ptr:
    "Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxNext_C
       (Scheduler_V611_Parse.xLIST_C.xListEnd_C
         (h_val ?heap Scheduler_V611_Parse.xPendingReadyList_')) =
     scheduler_event_item_ptr (sd_tcb_ptr D t')"
    using head_item by (simp add: scheduler_list_head_item_def)
  have next_pending: "t' \<in> set (rpc_tasks C)"
    using tasks by simp
  have next_live: "t' \<in> rpc_live C"
    by (rule resume_pending_gate_pending_liveD[OF rel next_pending])
  have observation:
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a"
    by (rule resume_pending_gate_task_observationD[OF rel])
  have next_live_abs: "t' \<in> sa_live a"
    using rel next_live
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  have event_guard:
    "c_guard (scheduler_event_item_ptr (sd_tcb_ptr D t'))"
    using TaskObservationRel_liveD[OF observation next_live_abs] by blast
  have event_owner:
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val ?heap (scheduler_event_item_ptr (sd_tcb_ptr D t'))) =
     PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
       (sd_tcb_ptr D t')"
    by (rule resume_pending_inserted_event_owner_observationD[
      OF rel tasks_cons next_pending])
  show ?thesis
    unfolding resume_pending_generated_head_read_def
    apply runs_to_vcg
    using count_nonzero head_ptr event_guard event_owner
    by simp_all
qed

end
