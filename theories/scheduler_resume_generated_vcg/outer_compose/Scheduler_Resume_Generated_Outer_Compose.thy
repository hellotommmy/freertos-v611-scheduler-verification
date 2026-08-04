theory Scheduler_Resume_Generated_Outer_Compose
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Missed_Loop.Scheduler_Resume_Generated_Missed_Loop"
begin

text \<open>
  Composition of the generated \<open>xTaskResumeAll'\<close> wrapper down to the
  missed-tick segment.  The theorem executes the critical-section entry,
  the suspension decrement, both population branches, the initial pending
  head read and the complete pending drain loop, and hands the exit state
  to an arbitrary continuation triple at the drained gate state.  The
  continuation premise covers the missed-tick replay segment, the final
  yield branch, the critical-section exit and the return value; its
  concrete discharge needs the still-open unlocked-tick source summary,
  so it stays a premise, exactly like the repository's other honest
  handoffs.  No task list, priority pattern, tick debt or heap layout is
  fixed anywhere.
\<close>

definition resume_after_drain_continuation ::
  "int \<Rightarrow>
   (int, Scheduler_V611_Parse.globals) res_monad"
where
  "resume_after_drain_continuation xYieldRequired = do {
     xYieldRequired \<leftarrow> condition
       (\<lambda>s. 0 < Scheduler_V611_Parse.globals.uxMissedTicks_' s)
       (do {
          whileLoop resume_missed_generated_cond
            resume_missed_generated_body ();
          return 1
        })
       (return xYieldRequired);
     condition
       (\<lambda>s. xYieldRequired = 1 \<or>
          Scheduler_V611_Parse.globals.xMissedYield_' s = 1)
       (do {
          modify (Scheduler_V611_Parse.globals.xMissedYield_'_update
            (\<lambda>_. 0));
          ret \<leftarrow> Scheduler_V611_Delay_Translation.eal6_port_yield';
          return 1
        })
       (return 0)
   }"

lemma resume_pending_generated_cond_fold:
  "(\<lambda>(pxTCB, xYieldRequired) s. pxTCB \<noteq> NULL) =
     resume_pending_generated_cond"
  by (simp add: fun_eq_iff resume_pending_generated_cond_def
      split: prod.split)

lemma resume_pending_generated_body_fold:
  "(\<lambda>(pxTCB, xYieldRequired). do {
      guard (\<lambda>_. c_guard pxTCB);
      ret \<leftarrow> Scheduler_V611_Delay_Translation.vListRemove'
        (PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
          &(pxTCB\<rightarrow>[''xEventListItem_C'']));
      ret \<leftarrow> Scheduler_V611_Delay_Translation.vListRemove'
        (PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
          &(pxTCB\<rightarrow>[''xGenericListItem_C'']));
      condition
        (\<lambda>s. Scheduler_V611_Parse.globals.uxTopReadyPriority_' s <
          Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
            (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
              pxTCB))
        (modify (\<lambda>s. s\<lparr>
          Scheduler_V611_Parse.globals.uxTopReadyPriority_' :=
            Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
              (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
                pxTCB)\<rparr>))
        skip;
      x \<leftarrow> guard
        (\<lambda>s. Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
          (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
            pxTCB) < 4);
      guard (\<lambda>s. c_guard Scheduler_V611_Parse.pxReadyTasksLists_');
      pxList \<leftarrow> gets (\<lambda>s.
        array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_' False
          (unat
            (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
              (h_val (hrs_mem
                (Scheduler_V611_Parse.globals.t_hrs_' s)) pxTCB))));
      ret \<leftarrow> Scheduler_V611_Delay_Translation.vListInsertEnd'
        pxList
        (PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
          &(pxTCB\<rightarrow>[''xGenericListItem_C'']));
      guard (\<lambda>s. c_guard
        (Scheduler_V611_Parse.globals.pxCurrentTCB_' s));
      xYieldRequired \<leftarrow> condition
        (\<lambda>s. Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
            (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
              (Scheduler_V611_Parse.globals.pxCurrentTCB_' s)) \<le>
          Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
            (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
              pxTCB))
        (return 1)
        (return xYieldRequired);
      ret \<leftarrow> resume_pending_generated_head_read;
      return
        (PTR_COERCE(unit \<rightarrow>
           Scheduler_V611_Parse.tskTaskControlBlock_C) ret,
         xYieldRequired)
    }) = resume_pending_generated_body"
  by (simp add: fun_eq_iff resume_pending_generated_body_def
      split: prod.split)

lemma resume_missed_generated_cond_fold:
  "(\<lambda>_ s. 0 < Scheduler_V611_Parse.globals.uxMissedTicks_' s) =
     resume_missed_generated_cond"
  by (simp add: fun_eq_iff resume_missed_generated_cond_def)

lemma resume_missed_generated_body_fold:
  "(\<lambda>_. do {
      ret \<leftarrow> Scheduler_V611_Delay_Translation.vTaskIncrementTick';
      modify (Scheduler_V611_Parse.globals.uxMissedTicks_'_update
        (\<lambda>a. a - 1))
    }) = resume_missed_generated_body"
  by (simp add: fun_eq_iff resume_missed_generated_body_def)

definition resume_outer_program ::
  "(int, Scheduler_V611_Parse.globals) res_monad"
where
  "resume_outer_program = do {
     ret \<leftarrow> Scheduler_V611_Tick_Translation.eal6_port_enter_critical';
     modify (Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update
       (\<lambda>a. a - 1));
     xAlreadyYielded \<leftarrow> condition
       (\<lambda>s. Scheduler_V611_Parse.globals.uxSchedulerSuspended_' s = 0)
       (condition
         (\<lambda>s. 0 < Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' s)
         (do {
            guard (\<lambda>s. c_guard Scheduler_V611_Parse.xPendingReadyList_');
            ret \<leftarrow> resume_pending_generated_head_read;
            (pxTCB, xYieldRequired) \<leftarrow>
              whileLoop resume_pending_generated_cond
                resume_pending_generated_body
                (PTR_COERCE(unit \<rightarrow>
                   Scheduler_V611_Parse.tskTaskControlBlock_C) ret, 0);
            resume_after_drain_continuation xYieldRequired
          })
         (return 0))
       (return 0);
     ret \<leftarrow> Scheduler_V611_Tick_Translation.eal6_port_exit_critical';
     return xAlreadyYielded
   }"

lemma xTaskResumeAll_program_eq:
  "Scheduler_V611_Delay_Translation.xTaskResumeAll' =
     resume_outer_program"
  by (simp add: Scheduler_V611_Delay_Translation.xTaskResumeAll'_def
      resume_outer_program_def
      resume_after_drain_continuation_def
      resume_pending_generated_head_read_def
      resume_pending_generated_body_fold[symmetric]
      resume_pending_generated_cond_fold[symmetric]
      resume_missed_generated_cond_fold[symmetric]
      resume_missed_generated_body_fold[symmetric])

lemma resume_generated_ptr_coerce_null:
  "PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.tskTaskControlBlock_C)
     NULL = NULL"
  by simp

lemma resume_generated_ptr_coerce_inverse:
  "PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.tskTaskControlBlock_C)
     (PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
        p) = p"
  by simp

lemma resume_pending_generated_head_read_uniform:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
  shows
    "resume_pending_generated_head_read \<bullet> c
     \<lbrace>\<lambda>r s. \<exists>u. r = Result u \<and> s = c \<and>
        PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.tskTaskControlBlock_C)
          u = resume_pending_next_head_tcb D (rpc_tasks C)\<rbrace>"
proof (cases "rpc_tasks C")
  case Nil
  show ?thesis
    apply (rule runs_to_weaken
        [OF resume_pending_generated_head_read_empty[OF rel Nil roots]])
    by (simp add: Nil resume_pending_next_head_tcb_def)
next
  case (Cons t rest)
  show ?thesis
    apply (rule runs_to_weaken
        [OF resume_pending_generated_head_read_nonempty
          [OF rel Cons roots]])
    by (simp add: Cons resume_pending_next_head_tcb_def)
qed

text \<open>
  The gate relation reads the heap, the current-task pointer and the
  scheduler scalars; it never reads the port's critical-section depth or
  interrupt flag, so it is invariant under updates of those two globals.
\<close>

lemma scheduler_lists_rel_critical_frame':
  "scheduler_lists_rel D R
     (Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update h
        (Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_'_update
           f (Scheduler_V611_Parse.globals.eal6_port_critical_depth_'_update
              g c))) a \<longleftrightarrow>
   scheduler_lists_rel D R
     (Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update h c) a"
  by (simp add: scheduler_lists_rel_def)

lemma scheduler_role_rel_critical_frame':
  "scheduler_role_rel R
     (Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update h
        (Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_'_update
           f (Scheduler_V611_Parse.globals.eal6_port_critical_depth_'_update
              g c))) a \<longleftrightarrow>
   scheduler_role_rel R
     (Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update h c) a"
  by (simp add: scheduler_role_rel_def)

lemma scheduler_scalar_rel_critical_frame':
  "scheduler_scalar_rel
     (Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update h
        (Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_'_update
           f (Scheduler_V611_Parse.globals.eal6_port_critical_depth_'_update
              g c))) a \<longleftrightarrow>
   scheduler_scalar_rel
     (Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update h c) a"
  by (simp add: scheduler_scalar_rel_def)

lemma scheduler_current_rel_critical_frame':
  "scheduler_current_rel D
     (Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update h
        (Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_'_update
           f (Scheduler_V611_Parse.globals.eal6_port_critical_depth_'_update
              g c))) a \<longleftrightarrow>
   scheduler_current_rel D
     (Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update h c) a"
  by (simp add: scheduler_current_rel_def split: option.split)

lemma resume_pending_gate_critical_frame':
  "resume_pending_gate_entry_rel D R
     (Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update h
        (Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_'_update
           f (Scheduler_V611_Parse.globals.eal6_port_critical_depth_'_update
              g c))) a C S generic_raw event_raw \<longleftrightarrow>
   resume_pending_gate_entry_rel D R
     (Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update h c)
     a C S generic_raw event_raw"
  unfolding resume_pending_gate_entry_rel_def Let_def
  by (simp add: scheduler_lists_rel_critical_frame'
      scheduler_role_rel_critical_frame'
      scheduler_scalar_rel_critical_frame'
      scheduler_current_rel_critical_frame')

lemma resume_pending_gate_live_nonzero_count:
  assumes rel:
    "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows "Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c \<noteq> 0"
proof -
  have scalar: "scheduler_scalar_rel c a"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def
    by blast
  have count:
    "unat (Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c) =
       card (sa_live a)"
    using scalar unfolding scheduler_scalar_rel_def by blast
  obtain current where cur_live: "current \<in> rpc_live C"
    using resume_pending_gate_current_absD[OF rel] by blast
  have live_eq: "rpc_live C = sa_live a"
    by (rule resume_pending_gate_live_absD[OF rel])
  have finite_live: "finite (sa_live a)"
  proof -
    have wf: "core_wf a"
      using rel
      unfolding resume_pending_gate_entry_rel_def Let_def
      by blast
    show ?thesis using wf unfolding core_wf_def by blast
  qed
  have nonempty: "sa_live a \<noteq> {}"
    using cur_live live_eq by auto
  have "card (sa_live a) \<noteq> 0"
    using finite_live nonempty by auto
  then show ?thesis
    using count by (metis unat_eq_zero)
qed

lemma resume_pending_gate_suspend_zeroD:
  assumes rel:
    "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c = 0"
proof -
  have scalar: "scheduler_scalar_rel c a"
    and depth: "sa_suspend_depth a = 0"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def
    by blast+
  have "unat (Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c) = 0"
    using scalar depth unfolding scheduler_scalar_rel_def by simp
  then show ?thesis by (simp add: unat_eq_zero)
qed

lemma runs_to_exit_return_lift:
  assumes h:
    "Scheduler_V611_Tick_Translation.eal6_port_exit_critical' \<bullet> s
       \<lbrace>\<lambda>r. Q (Result v)\<rbrace>"
  shows
    "(do {
        ret \<leftarrow> Scheduler_V611_Tick_Translation.eal6_port_exit_critical';
        return v
      }) \<bullet> s \<lbrace>Q\<rbrace>"
  apply (rule runs_to_bind_res)
  apply (rule runs_to_weaken[OF h])
  by (clarsimp simp: runs_to_iff)

theorem xTaskResumeAll_drain_composed:
  fixes Q
  assumes rel:
      "resume_pending_gate_entry_rel D R
         (Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update
            (\<lambda>n. n - 1) c) a C S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
    and cont:
      "\<And>c' C' S' gr' er' yw.
         resume_pending_gate_entry_rel D R c'
           (drain_pending_abs a) C' S' gr' er' \<Longrightarrow>
         rpc_tasks C' = [] \<Longrightarrow>
         rpc_live C' = rpc_live C \<Longrightarrow>
         rpc_current_priority C' = rpc_current_priority C \<Longrightarrow>
         rpc_priority C' = rpc_priority C \<Longrightarrow>
         ((yw \<noteq> 0) \<longleftrightarrow> resume_pending_requires_yield a) \<Longrightarrow>
         (do {
            xAlreadyYielded \<leftarrow> resume_after_drain_continuation yw;
            ret \<leftarrow> Scheduler_V611_Tick_Translation.eal6_port_exit_critical';
            return xAlreadyYielded
          }) \<bullet> c' \<lbrace>Q\<rbrace>"
  shows
    "Scheduler_V611_Delay_Translation.xTaskResumeAll' \<bullet> c \<lbrace>Q\<rbrace>"
proof -
  note rel1 = rel
  note rel3 = resume_pending_gate_critical_frame'[THEN iffD2, OF rel1]
  have count_pos:
    "Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c \<noteq> 0"
    using resume_pending_gate_live_nonzero_count[OF rel1] by simp
  have susp_dec_zero:
    "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c - 1 = 0"
    using resume_pending_gate_suspend_zeroD[OF rel1] by simp
  have suspended:
    "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c = 1"
    using susp_dec_zero by (metis eq_iff_diff_eq_0)
  show ?thesis
    unfolding xTaskResumeAll_program_eq resume_outer_program_def
      Scheduler_V611_Tick_Translation.eal6_port_enter_critical'_def
    apply runs_to_vcg
    subgoal
      by (rule resume_pending_gate_source_pending_guardD[OF rel1 roots])
    subgoal
      apply (rule runs_to_weaken
          [OF resume_pending_generated_head_read_uniform[OF rel3 roots]])
      apply clarsimp
      apply (rule runs_to_bind_res)
      apply (rule runs_to_weaken
          [OF resume_pending_generated_loop_drain_pending_abs
            [OF rel3 roots]])
      apply clarsimp
      apply (rule runs_to_weaken)
       apply (rule cont[unfolded runs_to_bind_iff])
            apply assumption
           apply assumption
          apply assumption
         apply assumption
        apply assumption
       apply simp
      apply (auto split: exception_or_result_splits prod.splits
          dest!: runs_to_exit_return_lift)
      done
    subgoal
      using count_pos by (simp add: word_neq_0_conv)
    subgoal
      using suspended by simp
    done
qed

end
