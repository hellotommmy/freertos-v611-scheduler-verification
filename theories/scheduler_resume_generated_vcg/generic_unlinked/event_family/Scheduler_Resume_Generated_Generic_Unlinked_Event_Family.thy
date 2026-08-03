theory Scheduler_Resume_Generated_Generic_Unlinked_Event_Family
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Event_Heap_Frame.Scheduler_Resume_Generated_Event_Heap_Frame"
begin

lemma resume_pending_event_raw_after_storage_subset:
  "raw_xlist_storage e
      (resume_pending_event_raw_after C D t event_raw e) \<subseteq>
   raw_xlist_storage e (event_raw e)"
proof -
  have ring_subset:
    "set (ring (resume_pending_event_raw_after C D t event_raw e))
       \<subseteq> set (ring (event_raw e))"
  proof (cases "e = rpc_pending_root C")
    case True
    show ?thesis
      using set_remove1_subset[of "event_item_raw_ptr D t"
        "ring (event_raw e)"] True
      by (simp add: resume_pending_event_raw_after_def
          event_remove_raw_family_def list_remove_abs_def)
  next
    case False
    then show ?thesis
      by (simp add: resume_pending_event_raw_after_def
          event_remove_raw_family_def)
  qed
  show ?thesis
    unfolding raw_xlist_storage_def
    using ring_subset by blast
qed

lemma resume_pending_generic_remove_event_storage_frame:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and root: "e \<in> rpc_event_roots C"
    and address:
      "address \<in> raw_xlist_storage e
        (resume_pending_event_raw_after C D t event_raw e)"
  shows
    "resume_pending_generic_remove_heap D t c address =
       resume_pending_event_remove_heap D t c address"
proof -
  let ?hE = "resume_pending_event_remove_heap D t c"
  let ?owner = "rpc_generic_owner C t"
  let ?p = "resume_pending_generic_raw_ptr D t"
  have owner_entry:
    "scheduler_delay_owner_entry_rel ?hE (rpc_generic_roots C)
       generic_raw ?owner ?p"
    by (rule resume_pending_event_remove_generic_owner_frame[OF rel tasks])
  have owner_root: "?owner \<in> rpc_generic_roots C"
    using owner_entry by (simp add: scheduler_delay_owner_entry_rel_def)
  have source_rel: "raw_xlist_rel ?hE ?owner (generic_raw ?owner)"
    by (rule resume_pending_event_remove_generic_root_frame[
      OF rel tasks owner_root])
  have member: "?p \<in> set (ring (generic_raw ?owner))"
    by (rule scheduler_delay_owner_entry_member[OF owner_entry])
  have cross:
    "raw_xlist_storage ?owner (generic_raw ?owner) \<inter>
       raw_xlist_storage e (event_raw e) = {}"
    using rel owner_root root
    unfolding resume_pending_gate_entry_rel_def Let_def
    by blast
  have footprint:
    "raw_remove_exact_write_footprint ?hE ?owner ?p \<subseteq>
       raw_xlist_storage ?owner (generic_raw ?owner)"
    by (rule raw_remove_exact_footprint_subset_storage[
      OF source_rel member])
  have old_storage:
    "address \<in> raw_xlist_storage e (event_raw e)"
    using resume_pending_event_raw_after_storage_subset[
      where e=e and C=C and D=D and t=t and event_raw=event_raw]
      address by blast
  have outside:
    "address \<notin> raw_remove_exact_write_footprint ?hE ?owner ?p"
    using footprint cross old_storage by blast
  show ?thesis
    unfolding resume_pending_generic_remove_heap_def
    by (rule raw_remove_concrete_heap_exact_external_frame[
      OF source_rel member outside])
qed

lemma resume_pending_generic_remove_event_item_frame:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and live: "u \<in> rpc_live C"
  shows
    "h_val (resume_pending_generic_remove_heap D t c)
       (event_item_raw_ptr D u) =
     h_val (resume_pending_event_remove_heap D t c)
       (event_item_raw_ptr D u)"
proof -
  let ?hE = "resume_pending_event_remove_heap D t c"
  let ?owner = "rpc_generic_owner C t"
  let ?p = "resume_pending_generic_raw_ptr D t"
  let ?q = "event_item_raw_ptr D u"
  have owner_entry:
    "scheduler_delay_owner_entry_rel ?hE (rpc_generic_roots C)
       generic_raw ?owner ?p"
    by (rule resume_pending_event_remove_generic_owner_frame[OF rel tasks])
  have owner_root: "?owner \<in> rpc_generic_roots C"
    using owner_entry by (simp add: scheduler_delay_owner_entry_rel_def)
  have member: "?p \<in> set (ring (generic_raw ?owner))"
    by (rule scheduler_delay_owner_entry_member[OF owner_entry])
  have managed: "?q \<in> universal_managed_nodes (rpc_live C) D"
    using live
    by (auto simp: event_item_raw_ptr_def universal_managed_nodes_def)
  have nonmember: "?q \<notin> set (ring (generic_raw ?owner))"
    by (rule resume_pending_gate_event_notin_generic_rootD[
      OF rel live owner_root])
  have bytes:
    "\<forall>address\<in>raw_item_region ?q.
       raw_remove_concrete_heap ?hE ?p address = ?hE address"
    using raw_remove_family_sibling_item_priority_byte_frame[
      OF resume_pending_event_remove_generic_family_frame[OF rel tasks]
      owner_root member managed nonmember live]
    by blast
  show ?thesis
    unfolding resume_pending_generic_remove_heap_def
  proof (rule delay_h_val_region_cong)
    fix address
    assume "address \<in> {ptr_val ?q..+size_of TYPE(xLIST_ITEM_C)}"
    then show "raw_remove_concrete_heap ?hE ?p address = ?hE address"
      using bytes by (simp add: raw_item_region_def)
  qed
qed

lemma resume_pending_generic_remove_event_family_frame:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "scheduler_event_root_family_rel D
       (resume_pending_generic_remove_heap D t c)
       (rpc_event_roots C) (rpc_pending_root C)
       (resume_pending_event_raw_after C D t event_raw)
       (rps_event_family (resume_pending_event_unlink_state C t S))
       (rpc_live C) (rpc_K_E C)"
proof -
  have event:
    "scheduler_event_root_family_rel D
       (resume_pending_event_remove_heap D t c)
       (rpc_event_roots C) (rpc_pending_root C)
       (resume_pending_event_raw_after C D t event_raw)
       (rps_event_family (resume_pending_event_unlink_state C t S))
       (rpc_live C) (rpc_K_E C)"
    using resume_pending_event_remove_family_post[OF rel tasks] by blast
  show ?thesis
    by (rule scheduler_event_root_family_heap_frameI[
      OF event
        resume_pending_generic_remove_event_storage_frame[OF rel tasks]
        resume_pending_generic_remove_event_item_frame[OF rel tasks]])
qed

end
