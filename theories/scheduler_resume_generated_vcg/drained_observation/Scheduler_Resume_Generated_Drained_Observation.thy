theory Scheduler_Resume_Generated_Drained_Observation
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Drained_Owner_Frames.Scheduler_Resume_Generated_Drained_Owner_Frames"
begin

text \<open>
  The full task observation relation is re-established at the drained
  state.  Guards and abstract priorities are heap-independent; the priority
  words survive through the existing priority frames; and the owner
  projections of both embedded items survive through the owner frames of
  the previous theory.  The relation holds against the unchanged abstract
  state: draining moves list nodes, but no TCB identity, priority payload
  or owner field.
\<close>

lemma resume_pending_drained_priority_chain:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and live: "u \<in> rpc_live C"
  shows
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
         (sd_tcb_ptr D u)) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (sd_tcb_ptr D u))"
  using resume_pending_ready_insert_priority_frame[OF rel tasks live]
    resume_pending_generic_remove_priority_frame[OF rel tasks live]
    resume_pending_event_remove_priority_frame[OF rel tasks live]
  by simp

lemma resume_pending_drained_generic_owner_chain:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and live: "u \<in> rpc_live C"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
         (scheduler_generic_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (scheduler_generic_item_ptr (sd_tcb_ptr D u)))"
  using resume_pending_ready_insert_generic_owner_live[OF rel tasks live]
    resume_pending_generic_remove_generic_owner_live[OF rel tasks live]
    resume_pending_event_remove_generic_owner_live[OF rel tasks live]
  by simp

lemma resume_pending_drained_event_owner_chain:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and live: "u \<in> rpc_live C"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
         (scheduler_event_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (scheduler_event_item_ptr (sd_tcb_ptr D u)))"
  using resume_pending_ready_insert_event_owner_live[OF rel tasks live]
    resume_pending_generic_remove_event_owner_live[OF rel tasks live]
    resume_pending_event_remove_event_owner_live[OF rel tasks live]
  by simp

section \<open>The task observation relation at the drained state\<close>

theorem resume_pending_drained_task_observation:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c))) a"
proof -
  have observation:
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a"
    by (rule resume_pending_gate_task_observationD[OF rel])
  have live_eq: "rpc_live C = sa_live a"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  have fin: "finite (sa_live a)"
    using observation by (simp add: TaskObservationRel_def)
  have per:
    "\<forall>u\<in>sa_live a.
       c_guard (sd_tcb_ptr D u) \<and>
       c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D u)) \<and>
       c_guard (scheduler_event_item_ptr (sd_tcb_ptr D u)) \<and>
       sa_priority a u < 4 \<and>
       unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
           (resume_pending_ready_inserted_state D C t generic_raw c)))
           (sd_tcb_ptr D u))) = sa_priority a u \<and>
       Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
           (resume_pending_ready_inserted_state D C t generic_raw c)))
           (sd_tcb_ptr D u)) < 4 \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
           (resume_pending_ready_inserted_state D C t generic_raw c)))
           (scheduler_generic_item_ptr (sd_tcb_ptr D u))) =
         PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
           (sd_tcb_ptr D u) \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
           (resume_pending_ready_inserted_state D C t generic_raw c)))
           (scheduler_event_item_ptr (sd_tcb_ptr D u))) =
         PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
           (sd_tcb_ptr D u)"
  proof (intro ballI)
    fix u
    assume u_abs: "u \<in> sa_live a"
    have u_live: "u \<in> rpc_live C"
      using live_eq u_abs by simp
    note entry = TaskObservationRel_liveD[OF observation u_abs]
    note priority_chain =
      resume_pending_drained_priority_chain[OF rel tasks u_live]
    note generic_owner_chain =
      resume_pending_drained_generic_owner_chain[OF rel tasks u_live]
    note event_owner_chain =
      resume_pending_drained_event_owner_chain[OF rel tasks u_live]
    show
      "c_guard (sd_tcb_ptr D u) \<and>
       c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D u)) \<and>
       c_guard (scheduler_event_item_ptr (sd_tcb_ptr D u)) \<and>
       sa_priority a u < 4 \<and>
       unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
           (resume_pending_ready_inserted_state D C t generic_raw c)))
           (sd_tcb_ptr D u))) = sa_priority a u \<and>
       Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
           (resume_pending_ready_inserted_state D C t generic_raw c)))
           (sd_tcb_ptr D u)) < 4 \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
           (resume_pending_ready_inserted_state D C t generic_raw c)))
           (scheduler_generic_item_ptr (sd_tcb_ptr D u))) =
         PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
           (sd_tcb_ptr D u) \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
           (resume_pending_ready_inserted_state D C t generic_raw c)))
           (scheduler_event_item_ptr (sd_tcb_ptr D u))) =
         PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
           (sd_tcb_ptr D u)"
      using entry priority_chain generic_owner_chain event_owner_chain
      by simp
  qed
  show ?thesis
    unfolding TaskObservationRel_def
    using fin per by blast
qed

end
