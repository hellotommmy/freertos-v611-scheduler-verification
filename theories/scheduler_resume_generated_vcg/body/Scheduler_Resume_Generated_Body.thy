theory Scheduler_Resume_Generated_Body
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Next_Head.Scheduler_Resume_Generated_Next_Head"
begin

text \<open>
  End-to-end execution of the complete generated pending-ready drain body.
  Every statement of \<open>resume_pending_generated_body\<close> is executed in source
  order from the gate entry state: the head guard, both generated removals,
  the top-priority conditional, the in-range and array guards, the
  destination read, the generated ready insertion, the current-task guard,
  the yield comparison, and the generated next-head re-read.  The theorem
  returns the exact loop-carried pair: the next pending task's TCB pointer
  (or NULL when the drained task was the last), and the conditional yield
  word.

  The head task, its priority, the current task, the live set, every ring
  population and the heap remain arbitrary.  The theorem executes one
  arbitrary iteration of the generated loop body; it does not close the
  loop, re-establish the gate entry relation for the drained context, or
  execute the generated outer \<open>xTaskResumeAll'\<close> wrapper.
\<close>

definition resume_pending_next_head_tcb ::
  "'tid scheduler_decode \<Rightarrow> 'tid list \<Rightarrow>
   Scheduler_V611_Parse.tskTaskControlBlock_C ptr"
where
  "resume_pending_next_head_tcb D rest =
     (case rest of [] \<Rightarrow> NULL | t' # _ \<Rightarrow> sd_tcb_ptr D t')"

section \<open>Elementary generated steps\<close>

lemma resume_pending_generated_entry_guard:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "guard (\<lambda>_. c_guard (sd_tcb_ptr D t)) \<bullet> c
     \<lbrace>\<lambda>r s. r = Result () \<and> s = c\<rbrace>"
proof -
  have live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  have observation:
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a"
    by (rule resume_pending_gate_task_observationD[OF rel])
  have live_abs: "t \<in> sa_live a"
    using rel live
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  have guard_t: "c_guard (sd_tcb_ptr D t)"
    using TaskObservationRel_liveD[OF observation live_abs] by blast
  show ?thesis
    apply runs_to_vcg
    using guard_t by simp_all
qed

lemma resume_pending_generated_priority_guard:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "guard
       (\<lambda>s. Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
           (sd_tcb_ptr D t)) < 4) \<bullet>
       (resume_pending_top_raised_state D t c)
     \<lbrace>\<lambda>r s. r = Result () \<and> s = resume_pending_top_raised_state D t c\<rbrace>"
proof -
  note priority = resume_pending_top_raised_head_priority[OF rel tasks]
  show ?thesis
    apply runs_to_vcg
    using priority by simp_all
qed

lemma resume_pending_generated_ready_array_guard_step:
  "guard (\<lambda>_. c_guard Scheduler_V611_Parse.pxReadyTasksLists_') \<bullet> s0
   \<lbrace>\<lambda>r s. r = Result () \<and> s = s0\<rbrace>"
  apply runs_to_vcg
  using generated_ready_array_guard by simp_all

lemma resume_pending_generated_destination_gets:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "gets (\<lambda>s.
       array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_' False
         (unat
           (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
             (h_val (hrs_mem
               (Scheduler_V611_Parse.globals.t_hrs_' s))
               (sd_tcb_ptr D t))))) \<bullet>
       (resume_pending_top_raised_state D t c)
     \<lbrace>\<lambda>r s.
       r = Result
         (array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_' False
           (rpc_priority C t))
       \<and> s = resume_pending_top_raised_state D t c\<rbrace>"
proof -
  note priority = resume_pending_top_raised_head_priority[OF rel tasks]
  have destination:
    "array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_' False
       (unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
           (resume_pending_top_raised_state D t c)))
           (sd_tcb_ptr D t)))) =
       sr_ready generated_scheduler_roots (rpc_priority C t)"
    using priority generated_ready_root_is_array_index by simp
  show ?thesis
    apply runs_to_vcg
    using destination by simp_all
qed

lemma resume_pending_generated_ready_insert_array_form:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and roots: "R = generated_scheduler_roots"
  shows
    "Scheduler_V611_Delay_Translation.vListInsertEnd'
       (array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_' False
         (rpc_priority C t))
       (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<bullet>
       (resume_pending_top_raised_state D t c)
     \<lbrace>\<lambda>r s.
       r = Result () \<and>
       s = resume_pending_ready_inserted_state D C t generic_raw c
     \<rbrace>"
  using resume_pending_generated_ready_insert_named[OF rel tasks roots]
  by simp

lemma resume_pending_generated_current_guard:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "guard (\<lambda>s. c_guard (Scheduler_V611_Parse.globals.pxCurrentTCB_' s))
       \<bullet> (resume_pending_ready_inserted_state D C t generic_raw c)
     \<lbrace>\<lambda>r s.
       r = Result () \<and>
       s = resume_pending_ready_inserted_state D C t generic_raw c\<rbrace>"
proof -
  note current = resume_pending_inserted_current_observationD[OF rel tasks]
  show ?thesis
    apply runs_to_vcg
    using current by simp_all
qed

lemma resume_pending_generated_yield_condition:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "condition
       (\<lambda>s. Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
           (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
             (Scheduler_V611_Parse.globals.pxCurrentTCB_' s)) \<le>
         Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
           (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
             (sd_tcb_ptr D t)))
       (return 1)
       (return y) \<bullet>
       (resume_pending_ready_inserted_state D C t generic_raw c)
     \<lbrace>\<lambda>r s.
       r = Result
         (if rpc_current_priority C \<le> rpc_priority C t then 1 else y) \<and>
       s = resume_pending_ready_inserted_state D C t generic_raw c\<rbrace>"
proof -
  note head = resume_pending_inserted_head_priorityD[OF rel tasks]
  note current = resume_pending_inserted_current_observationD[OF rel tasks]
  have compare:
    "(Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
        (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
          (resume_pending_ready_inserted_state D C t generic_raw c)))
          (Scheduler_V611_Parse.globals.pxCurrentTCB_'
            (resume_pending_ready_inserted_state D C t generic_raw c)))
      \<le>
      Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
        (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
          (resume_pending_ready_inserted_state D C t generic_raw c)))
          (sd_tcb_ptr D t))) =
     (rpc_current_priority C \<le> rpc_priority C t)"
    using head current by (simp add: word_le_nat_alt)
  show ?thesis
    apply runs_to_vcg
    using compare by simp_all
qed

lemma resume_pending_generated_head_read_drained:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and roots: "R = generated_scheduler_roots"
  shows
    "resume_pending_generated_head_read \<bullet>
       (resume_pending_ready_inserted_state D C t generic_raw c)
     \<lbrace>\<lambda>r s.
       r = Result
         (PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
           (resume_pending_next_head_tcb D rest)) \<and>
       s = resume_pending_ready_inserted_state D C t generic_raw c\<rbrace>"
proof (cases rest)
  case Nil
  have tasks_nil: "rpc_tasks C = [t]"
    using tasks Nil by simp
  have null:
    "PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
       (resume_pending_next_head_tcb D rest) = NULL"
    using Nil
    by (simp add: resume_pending_next_head_tcb_def ptr_eq_iff)
  show ?thesis
    apply (rule runs_to_weaken[
      OF resume_pending_generated_head_read_drained_empty[
        OF rel tasks_nil roots]])
    using null by simp
next
  case (Cons t' rest')
  have tasks_cons: "rpc_tasks C = t # t' # rest'"
    using tasks Cons by simp
  show ?thesis
    apply (rule runs_to_weaken[
      OF resume_pending_generated_head_read_drained_nonempty[
        OF rel tasks_cons roots]])
    using Cons by (simp add: resume_pending_next_head_tcb_def)
qed

section \<open>The complete generated drain body, executed end to end\<close>

theorem resume_pending_generated_body_exact:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and roots: "R = generated_scheduler_roots"
  shows
    "resume_pending_generated_body (sd_tcb_ptr D t, y) \<bullet> c
     \<lbrace>\<lambda>r s.
       r = Result
         (resume_pending_next_head_tcb D rest,
          if rpc_current_priority C \<le> rpc_priority C t then 1 else y) \<and>
       s = resume_pending_ready_inserted_state D C t generic_raw c \<and>
       scheduler_event_root_family_rel D
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
         (rpc_event_roots C) (rpc_pending_root C)
         (resume_pending_event_raw_after C D t event_raw)
         (rps_event_family (resume_pending_event_unlink_state C t S))
         (rpc_live C) (rpc_K_E C) \<and>
       Scheduler_V611_Parse.globals.pxCurrentTCB_' s =
         Scheduler_V611_Parse.globals.pxCurrentTCB_' c \<and>
       unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_' s) =
         rps_top (resume_pending_yield_check_state C t
           (resume_pending_ready_insert_state C t
             (resume_pending_raise_top_state C t
               (resume_pending_generic_unlink_state C t
                 (resume_pending_event_unlink_state C t S))))) \<and>
       resume_pending_loop_phase_inv C S [] (t # rest) RP_YieldChecked
         (resume_pending_yield_check_state C t
           (resume_pending_ready_insert_state C t
             (resume_pending_raise_top_state C t
               (resume_pending_generic_unlink_state C t
                 (resume_pending_event_unlink_state C t S)))))
     \<rbrace>"
proof -
  note entry_guard = resume_pending_generated_entry_guard[OF rel tasks]
  note event_cut =
    resume_pending_generated_event_unlinked_cutpoint[OF rel tasks]
  note generic_step =
    resume_pending_generic_remove_generated_after_event[OF rel tasks]
  note raise = resume_pending_generated_raise_top_exact[
    where D=D and t=t and c=c]
  note pri_guard = resume_pending_generated_priority_guard[OF rel tasks]
  note dest = resume_pending_generated_destination_gets[OF rel tasks]
  note insert = resume_pending_generated_ready_insert_array_form[
    OF rel tasks roots]
  note cur_guard = resume_pending_generated_current_guard[OF rel tasks]
  note yield = resume_pending_generated_yield_condition[OF rel tasks]
  note head = resume_pending_generated_head_read_drained[OF rel tasks roots]
  note family = resume_pending_ready_insert_event_family_frame[OF rel tasks]
  note phase = resume_pending_yield_checked_phaseD[OF rel tasks]
  have current_pres:
    "Scheduler_V611_Parse.globals.pxCurrentTCB_'
       (resume_pending_ready_inserted_state D C t generic_raw c) =
     Scheduler_V611_Parse.globals.pxCurrentTCB_' c"
    by (rule resume_pending_ready_inserted_pxCurrentTCB)
  have entry_top: "rps_top S = rpc_entry_top C"
    using resume_pending_gate_pure_entryD[OF rel]
    by (simp add: resume_pending_entry_rel_def)
  have top_sem:
    "unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_'
       (resume_pending_top_raised_state D t c)) =
     max (rpc_entry_top C) (rpc_priority C t)"
    using resume_pending_top_raised_semantics[OF rel tasks] by blast
  have snapshot_top:
    "rps_top (resume_pending_yield_check_state C t
       (resume_pending_ready_insert_state C t
         (resume_pending_raise_top_state C t
           (resume_pending_generic_unlink_state C t
             (resume_pending_event_unlink_state C t S))))) =
     max (rps_top S) (rpc_priority C t)"
    by (simp add: resume_pending_yield_check_state_def
        resume_pending_ready_insert_state_def
        resume_pending_raise_top_state_def
        resume_pending_generic_unlink_state_def
        resume_pending_event_unlink_state_def Let_def)
  have top_eq:
    "unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_'
       (resume_pending_ready_inserted_state D C t generic_raw c)) =
     rps_top (resume_pending_yield_check_state C t
       (resume_pending_ready_insert_state C t
         (resume_pending_raise_top_state C t
           (resume_pending_generic_unlink_state C t
             (resume_pending_event_unlink_state C t S)))))"
    using top_sem snapshot_top entry_top
    by (simp add: resume_pending_ready_inserted_top)
  show ?thesis
    unfolding resume_pending_generated_body_def
    apply (simp only: prod.case)
    apply (fold scheduler_event_item_ptr_def scheduler_generic_item_ptr_def)
    apply (fold resume_pending_generated_raise_top_def)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF entry_guard])
     apply (clarsimp split del: if_split)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF event_cut])
     apply (clarsimp split del: if_split)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF generic_step])
     apply (clarsimp split del: if_split)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF raise])
     apply (clarsimp split del: if_split)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF pri_guard])
     apply (clarsimp split del: if_split)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[
      OF resume_pending_generated_ready_array_guard_step])
     apply (clarsimp split del: if_split)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF dest])
     apply (clarsimp split del: if_split)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF insert])
     apply (clarsimp split del: if_split)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF cur_guard])
     apply (clarsimp split del: if_split)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF yield])
     apply (clarsimp split del: if_split)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF head])
     apply (clarsimp split del: if_split)
    apply runs_to_vcg
    using family current_pres top_eq phase
    by (simp_all split del: if_split)
qed

end
