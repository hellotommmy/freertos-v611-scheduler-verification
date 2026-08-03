theory Scheduler_Resume_Generated_Generic_Unlinked_Source
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Event_Unlinked.Scheduler_Resume_Generated_Event_Unlinked"
    "EAL6_FreeRTOS_V611_Scheduler_Node_Kind_Family_Remove_Preservation.Scheduler_Node_Kind_Family_Remove_Preservation"
begin

definition resume_pending_generic_remove_heap ::
  "'tid scheduler_decode \<Rightarrow> 'tid \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> heap_mem"
where
  "resume_pending_generic_remove_heap D t c =
     raw_remove_concrete_heap
       (resume_pending_event_remove_heap D t c)
       (resume_pending_generic_raw_ptr D t)"

definition resume_pending_generic_raw_after ::
  "('tid, xLIST_C ptr) resume_pending_context \<Rightarrow>
   'tid scheduler_decode \<Rightarrow> 'tid \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs)"
where
  "resume_pending_generic_raw_after C D t generic_raw =
     scheduler_family_remove_raw generic_raw (rpc_generic_owner C t)
       (resume_pending_generic_raw_ptr D t)"

lemma resume_pending_generic_abs_after:
  "scheduler_family_remove_abs
      (rps_generic_family (resume_pending_event_unlink_state C t S))
      (rpc_generic_owner C t) (Generic t) =
   rps_generic_family
      (resume_pending_generic_unlink_state C t
        (resume_pending_event_unlink_state C t S))"
  by (simp add: scheduler_family_remove_abs_def
      resume_pending_event_unlink_state_def
      resume_pending_generic_unlink_state_def)

lemma resume_pending_generic_unlinked_phaseD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_loop_phase_inv C S [] (t # rest)
       RP_GenericUnlinked
       (resume_pending_generic_unlink_state C t
         (resume_pending_event_unlink_state C t S))"
  by (rule resume_pending_loop_phase_inv_generic_step[
      OF resume_pending_event_unlinked_phaseD[OF rel tasks]])

lemma resume_pending_generic_remove_generated_after_event:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "Scheduler_V611_Delay_Translation.vListRemove'
       (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<bullet>
       (scheduler_mem_state (resume_pending_event_remove_heap D t c) c)
     \<lbrace>\<lambda>r s.
       r = Result () \<and>
       s = scheduler_mem_state
         (resume_pending_generic_remove_heap D t c) c
     \<rbrace>"
proof -
  let ?owner = "rpc_generic_owner C t"
  have owner_entry:
    "scheduler_delay_owner_entry_rel
       (resume_pending_event_remove_heap D t c)
       (rpc_generic_roots C) generic_raw ?owner
       (resume_pending_generic_raw_ptr D t)"
    by (rule resume_pending_event_remove_generic_owner_frame[OF rel tasks])
  have owner_root: "?owner \<in> rpc_generic_roots C"
    using owner_entry by (simp add: scheduler_delay_owner_entry_rel_def)
  have owner_source:
    "abi_list_ptr (resume_pending_owner_list_ptr R C t) = ?owner"
    by (rule resume_pending_gate_owner_list_ptrD[OF rel])
       (use tasks in simp)
  have raw:
    "raw_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (scheduler_mem_state (resume_pending_event_remove_heap D t c) c)))
       (abi_list_ptr (resume_pending_owner_list_ptr R C t))
       (generic_raw ?owner)"
    using resume_pending_event_remove_generic_root_frame[
        OF rel tasks owner_root]
      owner_source
    by simp
  have member:
    "abi_item_ptr (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<in>
       set (ring (generic_raw ?owner))"
    using scheduler_delay_owner_entry_member[OF owner_entry]
    by (simp add: resume_pending_generic_raw_ptr_def
        scheduler_generic_item_ptr_def abi_generic_list_item_ptr_def)
  note source = resume_pending_generic_remove_generated_interface[
    OF raw member]
  show ?thesis
    apply (rule runs_to_weaken[OF source])
    by (simp add: resume_pending_generic_remove_heap_def
        resume_pending_generic_raw_ptr_def scheduler_generic_item_ptr_def
        abi_generic_list_item_ptr_def)
qed

theorem resume_pending_generated_two_unlinks_exact:
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
         (resume_pending_generic_remove_heap D t c) c
     \<rbrace>"
proof -
  note event = resume_pending_generated_event_unlinked_cutpoint[OF rel tasks]
  note generic = resume_pending_generic_remove_generated_after_event[OF rel tasks]
  show ?thesis
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF event])
     apply clarsimp
    apply (rule runs_to_weaken[OF generic])
    by simp
qed

end
