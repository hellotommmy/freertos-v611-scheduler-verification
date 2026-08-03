theory Scheduler_Resume_Generated_Generic_Unlinked
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Generic_Unlinked_Event_Family.Scheduler_Resume_Generated_Generic_Unlinked_Event_Family"
begin

theorem resume_pending_generated_generic_unlinked_cutpoint:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "bind
       (Scheduler_V611_Delay_Translation.vListRemove'
         (scheduler_event_item_ptr (sd_tcb_ptr D t)))
       (\<lambda>_. Scheduler_V611_Delay_Translation.vListRemove'
         (scheduler_generic_item_ptr (sd_tcb_ptr D t))) \<bullet> c
     \<lbrace>\<lambda>r s.
       r = Result () \<and>
       s = scheduler_mem_state
         (resume_pending_generic_remove_heap D t c) c \<and>
       scheduler_node_kind_family_remove_post D
         (resume_pending_event_remove_heap D t c)
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
         (rpc_generic_roots C) generic_raw
         (rps_generic_family (resume_pending_event_unlink_state C t S))
         (rpc_live C) (rpc_generic_owner C t)
         (resume_pending_generic_raw_ptr D t) (Generic t) \<and>
       scheduler_event_root_family_rel D
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
         (rpc_event_roots C) (rpc_pending_root C)
         (resume_pending_event_raw_after C D t event_raw)
         (rps_event_family (resume_pending_event_unlink_state C t S))
         (rpc_live C) (rpc_K_E C) \<and>
       (\<forall>u\<in>rpc_live C.
         raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
           (resume_pending_generic_raw_ptr D u) = rpc_K_G C u) \<and>
       resume_pending_loop_phase_inv C S [] (t # rest)
         RP_GenericUnlinked
         (resume_pending_generic_unlink_state C t
           (resume_pending_event_unlink_state C t S))
     \<rbrace>"
proof -
  note source = resume_pending_generated_two_unlinks_exact[OF rel tasks]
  note generic = resume_pending_generic_remove_family_post[OF rel tasks]
  note event = resume_pending_generic_remove_event_family_frame[OF rel tasks]
  note phase = resume_pending_generic_unlinked_phaseD[OF rel tasks]
  show ?thesis
    apply (rule runs_to_weaken[OF source])
    using generic event phase
    by auto
qed

text \<open>
  This cutpoint symbolically executes the first two destructive calls in the
  actual pending-loop body.  No task, priority, owner, ready root, list length,
  key, cursor, heap or address is fixed.  The next proof obligation is the
  generated top-priority conditional followed by ready-list insertion.
\<close>

end
