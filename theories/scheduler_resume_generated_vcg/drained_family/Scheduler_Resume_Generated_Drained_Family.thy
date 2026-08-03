theory Scheduler_Resume_Generated_Drained_Family
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Drained_Observation.Scheduler_Resume_Generated_Drained_Observation"
begin

text \<open>
  The Generic raw family at the drained state.  After the two removals the
  awakened task's Generic item is globally unlinked -- exactly the
  remove-to-insert intermediate state the acceptance criteria require -- so
  the accepted insert-end preservation theorem applies and yields the whole
  post-insert family relation: the drained heap represents the removal
  family with the awakened task's item re-homed to the end of its priority's
  ready queue, with its wake key unchanged and its container now that queue.
\<close>

definition resume_pending_drained_generic_fam ::
  "('tid, xLIST_C ptr) resume_pending_context \<Rightarrow>
   'tid scheduler_decode \<Rightarrow> 'tid \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs)"
where
  "resume_pending_drained_generic_fam C D t c generic_raw =
     scheduler_family_insert_end_raw
       (resume_pending_generic_remove_heap D t c)
       (resume_pending_generic_raw_after C D t generic_raw)
       (rpc_ready_root C (rpc_priority C t))
       (resume_pending_generic_raw_ptr D t)"

lemma resume_pending_generic_unlinked_after_removal:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "raw_family_members (rpc_generic_roots C)
       (resume_pending_generic_raw_after C D t generic_raw)
       (resume_pending_generic_raw_ptr D t) = {}"
proof -
  note post = resume_pending_generic_remove_family_post[OF rel tasks]
  have unlinked:
    "raw_family_globally_unlinked
       (resume_pending_generic_remove_heap D t c)
       (rpc_generic_roots C)
       (scheduler_family_remove_raw generic_raw (rpc_generic_owner C t)
         (resume_pending_generic_raw_ptr D t))
       (resume_pending_generic_raw_ptr D t)"
    using post
    by (simp add: scheduler_node_kind_family_remove_post_def Let_def)
  show ?thesis
    using unlinked
    by (simp add: raw_family_globally_unlinked_def
        resume_pending_generic_raw_after_def)
qed

theorem resume_pending_drained_generic_family:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "scheduler_family_pre_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
       (rpc_generic_roots C)
       (resume_pending_drained_generic_fam C D t c generic_raw)
       (rpc_live C) D \<and>
     raw_family_members (rpc_generic_roots C)
       (resume_pending_drained_generic_fam C D t c generic_raw)
       (resume_pending_generic_raw_ptr D t) =
       {rpc_ready_root C (rpc_priority C t)} \<and>
     raw_key_at
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
       (resume_pending_generic_raw_ptr D t) =
       raw_key_at (resume_pending_generic_remove_heap D t c)
         (resume_pending_generic_raw_ptr D t) \<and>
     pvContainer_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
         (resume_pending_generic_raw_ptr D t)) =
       PTR_COERCE(xLIST_C \<rightarrow> unit)
         (rpc_ready_root C (rpc_priority C t))"
proof -
  let ?hR = "resume_pending_generic_remove_heap D t c"
  let ?target = "rpc_ready_root C (rpc_priority C t)"
  let ?fam = "resume_pending_generic_raw_after C D t generic_raw"
  let ?p = "resume_pending_generic_raw_ptr D t"
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
  have target: "?target \<in> rpc_generic_roots C"
    by (rule resume_pending_ready_target_in_roots[OF rel tasks])
  have fresh: "raw_fresh_for_insert ?target (ring (?fam ?target)) ?p"
    by (rule resume_pending_ready_fresh_after_removal[OF rel tasks])
  have p_managed: "?p \<in> universal_managed_nodes (rpc_live C) D"
    using t_live
    by (auto simp: resume_pending_generic_raw_ptr_def
        universal_managed_nodes_def)
  have absent:
    "raw_family_members (rpc_generic_roots C) ?fam ?p = {}"
    by (rule resume_pending_generic_unlinked_after_removal[OF rel tasks])
  note preserved = scheduler_family_insert_end_pre_rel_and_linked[
    OF pre target fresh p_managed absent]
  have heap_inserted:
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
       (resume_pending_ready_inserted_state D C t generic_raw c)) =
     raw_insert_concrete_heap ?hR ?target (?fam ?target) ?p"
    using heap_base
    by (simp add: resume_pending_ready_inserted_heap)
  show ?thesis
    using preserved heap_inserted
    by (simp add: resume_pending_drained_generic_fam_def)
qed

end
