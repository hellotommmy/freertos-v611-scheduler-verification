theory Scheduler_Resume_Generated_Ready_Insert
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Ready_Select.Scheduler_Resume_Generated_Ready_Select"
begin

text \<open>
  The generated pending-ready drain body inserts the awakened task's Generic
  item at the end of the selected ready queue.  This theory executes that
  call from the checked top-raised cutpoint state, for an arbitrary head task
  at an arbitrary in-range priority and an arbitrary legal ready-queue
  population.

  The two obligations of the general generated insert-end theorem are
  discharged here rather than assumed: the target ring relation comes from the
  post-removal family relation, and freshness is transported from the entry
  freshness fact, which survives the removal because the removal only rewrites
  the owner root and the owner root is not the destination ready queue.
\<close>

section \<open>The removal leaves the destination ready queue alone\<close>

lemma resume_pending_ready_target_not_owner:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows "rpc_generic_owner C t \<noteq> rpc_ready_root C (rpc_priority C t)"
proof -
  have live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  have pending: "t \<in> set (rpc_tasks C)"
    using tasks by simp
  have pure: "resume_pending_entry_rel C S"
    by (rule resume_pending_gate_pure_entryD[OF rel])
  show ?thesis
    using pure pending live
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_context_wf_def)
qed

lemma resume_pending_generic_raw_after_ready_target:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_generic_raw_after C D t generic_raw
       (rpc_ready_root C (rpc_priority C t)) =
     generic_raw (rpc_ready_root C (rpc_priority C t))"
  using resume_pending_ready_target_not_owner[OF rel tasks]
  by (simp add: resume_pending_generic_raw_after_def
      scheduler_family_remove_raw_def)

lemma resume_pending_ready_fresh_after_removal:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "raw_fresh_for_insert (rpc_ready_root C (rpc_priority C t))
       (ring (resume_pending_generic_raw_after C D t generic_raw
         (rpc_ready_root C (rpc_priority C t))))
       (resume_pending_generic_raw_ptr D t)"
  using resume_pending_gate_head_ready_freshD[OF rel tasks]
    resume_pending_generic_raw_after_ready_target[OF rel tasks]
  by simp

section \<open>Target ring relation at the top-raised cutpoint\<close>

lemma resume_pending_top_raised_generic_family:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "scheduler_family_pre_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_top_raised_state D t c)))
       (rpc_generic_roots C)
       (resume_pending_generic_raw_after C D t generic_raw)
       (rpc_live C) D"
proof -
  have heap:
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
       (resume_pending_top_raised_state D t c)) =
       resume_pending_generic_remove_heap D t c"
    using resume_pending_top_raised_semantics[OF rel tasks] by blast
  show ?thesis
    using resume_pending_generic_remove_family_post[OF rel tasks] heap
    by (simp add: scheduler_node_kind_family_remove_post_def Let_def
        resume_pending_generic_raw_after_def)
qed

lemma resume_pending_ready_target_in_roots:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows "rpc_ready_root C (rpc_priority C t) \<in> rpc_generic_roots C"
proof -
  have live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  have pure: "resume_pending_entry_rel C S"
    by (rule resume_pending_gate_pure_entryD[OF rel])
  show ?thesis
    using pure live
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_context_wf_def)
qed

lemma resume_pending_top_raised_target_ring_rel:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "raw_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_top_raised_state D t c)))
       (rpc_ready_root C (rpc_priority C t))
       (resume_pending_generic_raw_after C D t generic_raw
         (rpc_ready_root C (rpc_priority C t)))"
  using resume_pending_top_raised_generic_family[OF rel tasks]
    resume_pending_ready_target_in_roots[OF rel tasks]
  by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)

section \<open>The destination pointer in generated scheduler form\<close>

lemma resume_pending_ready_target_is_generated_root:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and roots: "R = generated_scheduler_roots"
  shows
    "rpc_ready_root C (rpc_priority C t) =
       abi_list_ptr
         (sr_ready generated_scheduler_roots (rpc_priority C t))"
proof -
  have live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  have source:
    "rpc_ready_root C (rpc_priority C t) =
       abi_list_ptr
         (array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_'
           False (rpc_priority C t))"
    by (rule resume_pending_gate_source_ready_rootD[OF rel roots live])
  show ?thesis
    using source by simp
qed

lemma resume_pending_generic_item_is_raw_ptr:
  "abi_item_ptr (scheduler_generic_item_ptr (sd_tcb_ptr D t)) =
     resume_pending_generic_raw_ptr D t"
  by (simp add: resume_pending_generic_raw_ptr_def)

section \<open>Exact generated ready insertion\<close>

theorem resume_pending_generated_ready_insert_exact:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and roots: "R = generated_scheduler_roots"
  shows
    "Scheduler_V611_Delay_Translation.vListInsertEnd'
       (sr_ready generated_scheduler_roots (rpc_priority C t))
       (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<bullet>
       (resume_pending_top_raised_state D t c)
     \<lbrace>\<lambda>r s.
       r = Result () \<and>
       s = scheduler_mem_state
         (raw_insert_concrete_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
             (resume_pending_top_raised_state D t c)))
           (rpc_ready_root C (rpc_priority C t))
           (resume_pending_generic_raw_after C D t generic_raw
             (rpc_ready_root C (rpc_priority C t)))
           (resume_pending_generic_raw_ptr D t))
         (resume_pending_top_raised_state D t c)
     \<rbrace>"
proof -
  note target = resume_pending_ready_target_is_generated_root[
    OF rel tasks roots]
  have ring_rel:
    "raw_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_top_raised_state D t c)))
       (abi_list_ptr
         (sr_ready generated_scheduler_roots (rpc_priority C t)))
       (resume_pending_generic_raw_after C D t generic_raw
         (rpc_ready_root C (rpc_priority C t)))"
    using resume_pending_top_raised_target_ring_rel[OF rel tasks] target
    by simp
  have fresh:
    "raw_fresh_for_insert
       (abi_list_ptr
         (sr_ready generated_scheduler_roots (rpc_priority C t)))
       (ring (resume_pending_generic_raw_after C D t generic_raw
         (rpc_ready_root C (rpc_priority C t))))
       (abi_item_ptr (scheduler_generic_item_ptr (sd_tcb_ptr D t)))"
    using resume_pending_ready_fresh_after_removal[OF rel tasks] target
    by (simp add: resume_pending_generic_raw_ptr_def)
  note source =
    scheduler_vListInsertEnd_general_exact_state[OF ring_rel fresh]
  show ?thesis
    apply (rule runs_to_weaken[OF source])
    using target
    by (simp add: resume_pending_generic_raw_ptr_def)
qed

end
