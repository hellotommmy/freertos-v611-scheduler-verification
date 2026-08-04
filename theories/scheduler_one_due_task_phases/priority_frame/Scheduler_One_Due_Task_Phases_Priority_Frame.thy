theory Scheduler_One_Due_Task_Phases_Priority_Frame
  imports
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_After_Event.Scheduler_One_Due_Task_Phases_After_Event"
begin

text \<open>
  Every live task's priority field survives both tick-body removals.  The
  Generic removal's footprint stays inside the delayed source's storage
  and the Event removal's footprint stays inside the linked owner's
  storage; both storages are separated from every priority field by the
  gate's geometry, so the four-byte field is untouched and the structure
  projection is transported by field-pointer congruence.  This is the
  observation the generated top-raise conditional, the in-range guard
  and the ready-array selection read after the removals.
\<close>

lemma one_due_gateH_source_memberD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "one_due_generic_raw_ptr D (odc_task C) \<in>
       set (ring (generic_raw (odc_delayed_root C)))"
proof -
  have owner:
    "scheduler_delay_owner_entry_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (odc_generic_roots C) generic_raw (odc_delayed_root C)
       (one_due_generic_raw_ptr D (odc_task C))"
    using rel
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  show ?thesis
    by (rule scheduler_delay_owner_entry_member[OF owner])
qed

lemma one_due_generic_remove_priority_byte_frame:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "u \<in> odc_live C"
  shows
    "\<forall>address\<in>universal_priority_field_region (sd_tcb_ptr D u).
       one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) address =
       hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c) address"
proof -
  have task_live: "odc_task C \<in> odc_live C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have managed:
    "event_item_raw_ptr D (odc_task C) \<in>
       universal_managed_nodes (odc_live C) D"
    using task_live
    by (auto simp: universal_managed_nodes_def event_item_raw_ptr_def)
  have nonmember:
    "event_item_raw_ptr D (odc_task C) \<notin>
       set (ring (generic_raw (odc_delayed_root C)))"
    by (rule one_due_gateH_event_notin_generic_rootD[OF rel task_live
      one_due_gateH_source_in_rootsD[OF rel]])
  show ?thesis
    unfolding one_due_generic_remove_heap_def
    using raw_remove_family_sibling_item_priority_byte_frame[
      OF one_due_gateH_generic_preD[OF rel]
        one_due_gateH_source_in_rootsD[OF rel]
        one_due_gateH_source_memberD[OF rel] managed nonmember live]
    by blast
qed

lemma one_due_gateH_event_preD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "scheduler_family_pre_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (odc_event_roots C) event_raw (odc_live C) D"
  using one_due_gateH_event_relD[OF rel]
  by (simp add: scheduler_event_root_family_rel_def)

lemma one_due_event_remove_priority_byte_frame:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C (DueEventLinked owner) S
       generic_raw event_raw"
    and live: "u \<in> odc_live C"
  shows
    "\<forall>address\<in>universal_priority_field_region (sd_tcb_ptr D u).
       raw_remove_concrete_heap
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
         (event_item_raw_ptr D (odc_task C)) address =
       one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) address"
proof (intro ballI)
  let ?hg = "one_due_generic_remove_heap D C
    (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
  let ?q = "event_item_raw_ptr D (odc_task C)"
  fix address
  assume address:
    "address \<in> universal_priority_field_region (sd_tcb_ptr D u)"
  have owner_facts:
    "raw_xlist_rel ?hg owner (event_raw owner) \<and>
     ?q \<in> set (ring (event_raw owner))"
    by (rule one_due_gateH_linked_event_after_genericD[OF rel])
  have owner_rel: "raw_xlist_rel ?hg owner (event_raw owner)"
    and member: "?q \<in> set (ring (event_raw owner))"
    using owner_facts by blast+
  have owner_root: "owner \<in> odc_event_roots C"
    by (rule one_due_gateH_linked_ownerD[OF rel])
  have footprint:
    "raw_remove_exact_write_footprint ?hg owner ?q \<subseteq>
       raw_xlist_storage owner (event_raw owner)"
    by (rule raw_remove_exact_footprint_subset_storage[
      OF owner_rel member])
  have disj:
    "raw_xlist_storage owner (event_raw owner) \<inter>
       universal_priority_field_region (sd_tcb_ptr D u) = {}"
    by (rule scheduler_family_target_storage_priority_disjoint[
      OF one_due_gateH_event_preD[OF rel] owner_root live])
  have outside:
    "address \<notin> raw_remove_exact_write_footprint ?hg owner ?q"
    using footprint disj address by blast
  show "raw_remove_concrete_heap ?hg ?q address = ?hg address"
    by (rule raw_remove_concrete_heap_exact_external_frame[
      OF owner_rel member outside])
qed

theorem one_due_gateH_priority_after_eventD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "u \<in> odc_live C"
  shows
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
         (sd_tcb_ptr D u)) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (sd_tcb_ptr D u))"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?hg = "one_due_generic_remove_heap D C ?h"
  let ?he = "one_due_event_remove_heap D C branch ?hg"
  let ?tp = "sd_tcb_ptr D u"
  have generic_bytes:
    "\<forall>address\<in>universal_priority_field_region ?tp.
       ?hg address = ?h address"
    by (rule one_due_generic_remove_priority_byte_frame[OF rel live])
  have bytes:
    "\<forall>address\<in>universal_priority_field_region ?tp.
       ?he address = ?h address"
  proof (cases branch)
    case DueEventNull
    then show ?thesis
      using generic_bytes
      by (simp add: one_due_event_remove_heap_def)
  next
    case (DueEventLinked owner)
    have rel_linked:
      "one_due_gateH_entry_rel D R c a C (DueEventLinked owner) S
         generic_raw event_raw"
      using rel DueEventLinked by simp
    have event_bytes:
      "\<forall>address\<in>universal_priority_field_region ?tp.
         raw_remove_concrete_heap ?hg
           (event_item_raw_ptr D (odc_task C)) address = ?hg address"
      by (rule one_due_event_remove_priority_byte_frame[
        OF rel_linked live])
    show ?thesis
      using generic_bytes event_bytes DueEventLinked
      by (simp add: one_due_event_remove_heap_def)
  qed
  have field_same:
    "h_val ?he (universal_priority_field_ptr ?tp) =
     h_val ?h (universal_priority_field_ptr ?tp)"
  proof (rule delay_h_val_region_cong)
    fix address
    assume "address \<in>
      {ptr_val (universal_priority_field_ptr ?tp)..+
         size_of TYPE(32 word)}"
    then show "?he address = ?h address"
      using bytes
      by (simp add: universal_priority_field_region_def)
  qed
  show ?thesis
    using field_same
    unfolding universal_priority_field_ptr_def
    by (simp only:
      Scheduler_V611_Parse.tskTaskControlBlock_C_h_val_fields(4))
qed

end
