theory Scheduler_Resume_Generated_Insert_Event_Family
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Owner_Frame.Scheduler_Resume_Generated_Owner_Frame"
begin

text \<open>
  The generated ready insertion writes only inside the selected ready
  queue's storage and the inserted Generic item's region.  Both are disjoint
  from every Event root's storage and from every live task's Event item, so
  the arbitrary Event-root family relation -- already transported across the
  two removals -- survives the insertion unchanged.
\<close>

section \<open>Event storage bytes survive the generated insertion\<close>

lemma resume_pending_ready_insert_event_storage_frame:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and root: "e \<in> rpc_event_roots C"
    and address:
      "address \<in> raw_xlist_storage e
        (resume_pending_event_raw_after C D t event_raw e)"
  shows
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
       (resume_pending_ready_inserted_state D C t generic_raw c)) address =
     resume_pending_generic_remove_heap D t c address"
proof -
  let ?hR = "resume_pending_generic_remove_heap D t c"
  let ?target = "rpc_ready_root C (rpc_priority C t)"
  let ?fam = "resume_pending_generic_raw_after C D t generic_raw"
  let ?p = "resume_pending_generic_raw_ptr D t"
  have heap_base:
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
       (resume_pending_top_raised_state D t c)) = ?hR"
    using resume_pending_top_raised_semantics[OF rel tasks] by blast
  have ring_rel: "raw_xlist_rel ?hR ?target (?fam ?target)"
    using resume_pending_top_raised_target_ring_rel[OF rel tasks]
      heap_base by simp
  have fresh: "raw_fresh_for_insert ?target (ring (?fam ?target)) ?p"
    by (rule resume_pending_ready_fresh_after_removal[OF rel tasks])
  have footprint:
    "raw_insert_end_exact_write_footprint ?hR ?target (?fam ?target) ?p
       \<subseteq> raw_xlist_storage ?target (?fam ?target) \<union>
         raw_item_region ?p"
    by (rule raw_insert_end_exact_footprint_subset_storage[OF ring_rel])
  have target_root: "?target \<in> rpc_generic_roots C"
    by (rule resume_pending_ready_target_in_roots[OF rel tasks])
  have target_entry:
    "?fam ?target = generic_raw ?target"
    by (rule resume_pending_generic_raw_after_ready_target[OF rel tasks])
  have cross_target:
    "raw_xlist_storage ?target (generic_raw ?target) \<inter>
       raw_xlist_storage e (event_raw e) = {}"
    using rel target_root root
    unfolding resume_pending_gate_entry_rel_def Let_def
    by blast
  have owner_entry:
    "scheduler_delay_owner_entry_rel
       (resume_pending_event_remove_heap D t c)
       (rpc_generic_roots C) generic_raw (rpc_generic_owner C t) ?p"
    by (rule resume_pending_event_remove_generic_owner_frame[OF rel tasks])
  have owner_root: "rpc_generic_owner C t \<in> rpc_generic_roots C"
    using owner_entry by (simp add: scheduler_delay_owner_entry_rel_def)
  have p_member: "?p \<in> set (ring (generic_raw (rpc_generic_owner C t)))"
    by (rule scheduler_delay_owner_entry_member[OF owner_entry])
  have p_in_owner_storage:
    "raw_item_region ?p \<subseteq>
       raw_xlist_storage (rpc_generic_owner C t)
         (generic_raw (rpc_generic_owner C t))"
    using p_member by (auto simp: raw_xlist_storage_def)
  have cross_owner:
    "raw_xlist_storage (rpc_generic_owner C t)
       (generic_raw (rpc_generic_owner C t)) \<inter>
       raw_xlist_storage e (event_raw e) = {}"
    using rel owner_root root
    unfolding resume_pending_gate_entry_rel_def Let_def
    by blast
  have old_storage:
    "address \<in> raw_xlist_storage e (event_raw e)"
    using resume_pending_event_raw_after_storage_subset[
      where e=e and C=C and D=D and t=t and event_raw=event_raw]
      address by blast
  have footprint_entry:
    "raw_insert_end_exact_write_footprint ?hR ?target (?fam ?target) ?p
       \<subseteq> raw_xlist_storage ?target (generic_raw ?target) \<union>
         raw_item_region ?p"
    using footprint target_entry by simp
  have outside:
    "address \<notin> raw_insert_end_exact_write_footprint
       ?hR ?target (?fam ?target) ?p"
    using footprint_entry cross_target p_in_owner_storage
      cross_owner old_storage by blast
  have byte:
    "raw_insert_concrete_heap ?hR ?target (?fam ?target) ?p address =
       ?hR address"
    by (rule raw_insert_concrete_heap_exact_external_frame[
      OF ring_rel fresh outside])
  show ?thesis
    using byte heap_base
    by (simp add: resume_pending_ready_inserted_heap)
qed

section \<open>Event items survive the generated insertion\<close>

lemma resume_pending_ready_insert_event_item_frame:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and live: "u \<in> rpc_live C"
  shows
    "h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
       (resume_pending_ready_inserted_state D C t generic_raw c)))
       (event_item_raw_ptr D u) =
     h_val (resume_pending_generic_remove_heap D t c)
       (event_item_raw_ptr D u)"
proof -
  let ?hR = "resume_pending_generic_remove_heap D t c"
  let ?target = "rpc_ready_root C (rpc_priority C t)"
  let ?fam = "resume_pending_generic_raw_after C D t generic_raw"
  let ?p = "resume_pending_generic_raw_ptr D t"
  let ?q = "event_item_raw_ptr D u"
  have t_live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  have heap_base:
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
       (resume_pending_top_raised_state D t c)) = ?hR"
    using resume_pending_top_raised_semantics[OF rel tasks] by blast
  have pre:
    "scheduler_family_pre_rel ?hR (rpc_generic_roots C) ?fam
       (rpc_live C) D"
    using resume_pending_top_raised_generic_family[OF rel tasks]
      heap_base by simp
  have target_root: "?target \<in> rpc_generic_roots C"
    by (rule resume_pending_ready_target_in_roots[OF rel tasks])
  have fresh: "raw_fresh_for_insert ?target (ring (?fam ?target)) ?p"
    by (rule resume_pending_ready_fresh_after_removal[OF rel tasks])
  have p_managed: "?p \<in> universal_managed_nodes (rpc_live C) D"
    using t_live
    by (auto simp: resume_pending_generic_raw_ptr_def
        universal_managed_nodes_def)
  have q_managed: "?q \<in> universal_managed_nodes (rpc_live C) D"
    using live
    by (auto simp: event_item_raw_ptr_def universal_managed_nodes_def)
  have p_q: "?p \<noteq> ?q"
    by (rule resume_pending_gate_generic_event_ptr_distinct[
      OF rel t_live live])
  have target_entry: "?fam ?target = generic_raw ?target"
    by (rule resume_pending_generic_raw_after_ready_target[OF rel tasks])
  have nonmember: "?q \<notin> set (ring (?fam ?target))"
    using resume_pending_gate_event_notin_generic_rootD[
      OF rel live target_root] target_entry by simp
  have bytes:
    "\<forall>address\<in>raw_item_region ?q.
       raw_insert_concrete_heap ?hR ?target (?fam ?target) ?p address =
       ?hR address"
    using raw_insert_end_family_sibling_item_priority_byte_frame[
      OF pre target_root fresh p_managed q_managed p_q nonmember live]
    by blast
  have heap_inserted:
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
       (resume_pending_ready_inserted_state D C t generic_raw c)) =
     raw_insert_concrete_heap ?hR ?target (?fam ?target) ?p"
    using heap_base
    by (simp add: resume_pending_ready_inserted_heap)
  have field_same:
    "h_val (raw_insert_concrete_heap ?hR ?target (?fam ?target) ?p) ?q =
     h_val ?hR ?q"
  proof (rule delay_h_val_region_cong)
    fix address
    assume "address \<in> {ptr_val ?q..+size_of TYPE(xLIST_ITEM_C)}"
    then show
      "raw_insert_concrete_heap ?hR ?target (?fam ?target) ?p address =
       ?hR address"
      using bytes by (simp add: raw_item_region_def)
  qed
  show ?thesis using field_same by (simp add: heap_inserted)
qed

section \<open>The Event family relation at the ready-inserted cutpoint\<close>

theorem resume_pending_ready_insert_event_family_frame:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "scheduler_event_root_family_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
       (rpc_event_roots C) (rpc_pending_root C)
       (resume_pending_event_raw_after C D t event_raw)
       (rps_event_family (resume_pending_event_unlink_state C t S))
       (rpc_live C) (rpc_K_E C)"
  by (rule scheduler_event_root_family_heap_frameI[
    OF resume_pending_generic_remove_event_family_frame[OF rel tasks]
      resume_pending_ready_insert_event_storage_frame[OF rel tasks]
      resume_pending_ready_insert_event_item_frame[OF rel tasks]])

end
