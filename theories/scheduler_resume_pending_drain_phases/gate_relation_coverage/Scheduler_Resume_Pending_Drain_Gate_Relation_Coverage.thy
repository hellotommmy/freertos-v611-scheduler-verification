theory Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Event.Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Event"
begin

lemma resume_pending_gate_empty_pending_countD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = []"
  shows
    "Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (sr_pending R)) = 0"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  have root: "rpc_pending_root C \<in> rpc_event_roots C"
    using resume_pending_gate_pure_entryD[OF rel]
    by (auto simp: resume_pending_entry_rel_def resume_pending_context_wf_def)
  have count:
    "unat (List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
       (h_val ?h (rpc_pending_root C))) =
       length (ring (rps_event_family S (rpc_pending_root C)))"
    by (rule scheduler_event_root_family_countD[
      OF resume_pending_gate_event_familyD[OF rel] root])
  have empty:
    "ring (rps_event_family S (rpc_pending_root C)) = []"
    using resume_pending_gate_pure_entryD[OF rel] tasks
    by (simp add: resume_pending_entry_rel_def)
  have root_eq:
    "rpc_pending_root C = abi_list_ptr (sr_pending R)"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def
    by blast
  have raw_zero:
    "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
       (h_val ?h (abi_list_ptr (sr_pending R))) = 0"
    using count empty root_eq by (simp add: unat_eq_0)
  show ?thesis
    using raw_zero by (simp only: abi_list_count_h_val)
qed

corollary resume_pending_gate_empty_source_pending_countD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = []"
    and roots: "R = generated_scheduler_roots"
  shows
    "Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         Scheduler_V611_Parse.xPendingReadyList_') = 0"
  using resume_pending_gate_empty_pending_countD[OF rel tasks] roots
  by simp

end
