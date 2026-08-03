theory Scheduler_Resume_Generated_Ready_Select
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Top_Raised.Scheduler_Resume_Generated_Top_Raised"
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Ready_Destination.Scheduler_Resume_Generated_Ready_Destination"
begin

text \<open>
  The generated pending-ready drain body continues, after the top-priority
  conditional, with its own in-range priority guard, the ready-array guard,
  and the destination read.  This theory executes exactly that fragment from
  the checked top-raised cutpoint state and identifies the selected queue as
  the indexed scheduler root at the head task's priority.

  The priority is not fixed: it is whatever the represented head task carries,
  and the source guard supplies the only bound used.
\<close>

definition resume_pending_generated_ready_select ::
  "'tid scheduler_decode \<Rightarrow> 'tid \<Rightarrow>
   (Scheduler_V611_Parse.xLIST_C ptr, Scheduler_V611_Parse.globals) res_monad"
where
  "resume_pending_generated_ready_select D t = do {
     x \<leftarrow> guard
       (\<lambda>s. Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
           (sd_tcb_ptr D t)) < 4);
     guard (\<lambda>_. c_guard Scheduler_V611_Parse.pxReadyTasksLists_');
     gets (\<lambda>s.
       array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_' False
         (unat
           (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
             (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
               (sd_tcb_ptr D t)))))
   }"

section \<open>Priority observation at the top-raised cutpoint\<close>

lemma resume_pending_top_raised_head_priority:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_top_raised_state D t c)))
         (sd_tcb_ptr D t)) < 4 \<and>
     unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_top_raised_state D t c)))
         (sd_tcb_ptr D t))) = rpc_priority C t"
proof -
  have heap:
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
       (resume_pending_top_raised_state D t c)) =
       resume_pending_generic_remove_heap D t c"
    using resume_pending_top_raised_semantics[OF rel tasks] by blast
  show ?thesis
    using resume_pending_two_removes_head_priorityD[OF rel tasks] heap
    by simp
qed

lemma resume_pending_head_priority_bound:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows "rpc_priority C t < 4"
  using resume_pending_gate_head_owner_priorityD[OF rel tasks] by blast

section \<open>Exact generated destination read\<close>

theorem resume_pending_generated_ready_select_exact:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_generated_ready_select D t \<bullet>
       (resume_pending_top_raised_state D t c)
     \<lbrace>\<lambda>r s.
       r = Result
         (sr_ready generated_scheduler_roots (rpc_priority C t)) \<and>
       s = resume_pending_top_raised_state D t c \<and>
       c_guard (sr_ready generated_scheduler_roots (rpc_priority C t))
     \<rbrace>"
proof -
  note priority = resume_pending_top_raised_head_priority[OF rel tasks]
  have bound: "rpc_priority C t < 4"
    by (rule resume_pending_head_priority_bound[OF rel tasks])
  have destination:
    "array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_' False
       (unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
           (resume_pending_top_raised_state D t c)))
           (sd_tcb_ptr D t)))) =
       sr_ready generated_scheduler_roots (rpc_priority C t)"
    using priority generated_ready_root_is_array_index by simp
  have guard_ready: "c_guard Scheduler_V611_Parse.pxReadyTasksLists_'"
    by (rule generated_ready_array_guard)
  have guard_destination:
    "c_guard (sr_ready generated_scheduler_roots (rpc_priority C t))"
    by (rule generated_ready_root_guard[OF bound])
  show ?thesis
    unfolding resume_pending_generated_ready_select_def
    apply runs_to_vcg
    using priority guard_ready destination guard_destination
    by simp_all
qed

section \<open>Separation of the selected queue\<close>

corollary resume_pending_generated_ready_select_member:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "sr_ready generated_scheduler_roots (rpc_priority C t)
       \<in> set (p2_physical_roots generated_scheduler_roots)"
  by (rule generated_ready_root_member[
        OF resume_pending_head_priority_bound[OF rel tasks]])

corollary resume_pending_generated_ready_select_separated:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and other: "lq \<in> set (p2_physical_roots generated_scheduler_roots)"
    and distinct:
      "sr_ready generated_scheduler_roots (rpc_priority C t) \<noteq> lq"
  shows
    "scheduler_list_region
       (sr_ready generated_scheduler_roots (rpc_priority C t))
     \<inter> scheduler_list_region lq = {}"
  by (rule generated_ready_root_disjoint[
        OF resume_pending_head_priority_bound[OF rel tasks] other distinct])

end
