theory Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Ownership
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Count.Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Count"
begin

lemma resume_pending_gate_head_liveD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows "t \<in> rpc_live C"
  using resume_pending_gate_pure_entryD[OF rel] tasks
  by (auto simp: resume_pending_entry_rel_def resume_pending_context_wf_def)

lemma resume_pending_gate_owner_list_ptrD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and pending: "t \<in> set (rpc_tasks C)"
  shows
    "abi_list_ptr (resume_pending_owner_list_ptr R C t) =
       rpc_generic_owner C t"
proof -
  have choices:
    "rpc_generic_owner C t \<in>
      {abi_list_ptr (sr_delayed_a R),
       abi_list_ptr (sr_delayed_b R),
       abi_list_ptr (sr_suspended R)}"
    using rel pending
    unfolding resume_pending_gate_entry_rel_def Let_def
    by blast
  show ?thesis
    using choices
    by (auto simp: resume_pending_owner_list_ptr_def)
qed

lemma resume_pending_gate_ready_list_ptrD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and live: "t \<in> rpc_live C"
  shows
    "abi_list_ptr (sr_ready R (rpc_priority C t)) =
       rpc_ready_root C (rpc_priority C t)"
proof -
  have ready_roots:
    "\<forall>u\<in>rpc_live C.
       rpc_ready_root C (rpc_priority C u) =
         abi_list_ptr (sr_ready R (rpc_priority C u))"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def
    by (elim conjE) assumption
  have forward:
    "rpc_ready_root C (rpc_priority C t) =
       abi_list_ptr (sr_ready R (rpc_priority C t))"
    using ready_roots live by blast
  show ?thesis by (rule forward[symmetric])
qed

lemma resume_pending_gate_head_generic_ownerD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "scheduler_delay_owner_entry_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (rpc_generic_roots C) generic_raw (rpc_generic_owner C t)
       (resume_pending_generic_raw_ptr D t) \<and>
     raw_family_insert_geometry (rpc_generic_roots C) generic_raw
       (resume_pending_generic_raw_ptr D t)"
  using rel tasks
  unfolding resume_pending_gate_entry_rel_def Let_def
  by auto

end
