theory Scheduler_P2_Control_Leaves
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Insert_Refinement.Scheduler_P2_Insert_Refinement"
begin

text \<open>
  Exact source leaves for the quiet scheduler-control path used by P2.  These
  theorems expose complete scheduler-global post states, so the later
  vTaskDelay composition does not need to reopen any callee body.
\<close>

definition p2_suspend_state ::
  "Scheduler_V611_Parse.globals \<Rightarrow> Scheduler_V611_Parse.globals"
where
  "p2_suspend_state c =
     Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update
       (\<lambda>n. n + 1) c"

definition p2_resume_quiet_state ::
  "Scheduler_V611_Parse.globals \<Rightarrow> Scheduler_V611_Parse.globals"
where
  "p2_resume_quiet_state c =
     Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update
       (\<lambda>n. n - 1) c"

definition p2_yield_state ::
  "Scheduler_V611_Parse.globals \<Rightarrow> Scheduler_V611_Parse.globals"
where
  "p2_yield_state c =
     Scheduler_V611_Parse.globals.eal6_port_yield_count_'_update
       (\<lambda>n. n + 1) c"

theorem scheduler_vTaskSuspendAll_exact:
  "Scheduler_V611_Delay_Translation.vTaskSuspendAll' \<bullet> c
   \<lbrace>\<lambda>r t. r = Result () \<and> t = p2_suspend_state c\<rbrace>"
  unfolding Scheduler_V611_Delay_Translation.vTaskSuspendAll'_def
    p2_suspend_state_def
  by runs_to_vcg

theorem scheduler_eal6_port_yield_exact:
  "Scheduler_V611_Delay_Translation.eal6_port_yield' \<bullet> c
   \<lbrace>\<lambda>r t. r = Result () \<and> t = p2_yield_state c\<rbrace>"
  unfolding Scheduler_V611_Delay_Translation.eal6_port_yield'_def
    p2_yield_state_def
  by runs_to_vcg

theorem scheduler_xTaskResumeAll_quiet_exact:
  assumes suspended:
      "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c = 1"
    and depth:
      "Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c = 0"
    and interrupts:
      "Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' c = 0"
    and pending_guard:
      "c_guard Scheduler_V611_Parse.xPendingReadyList_'"
    and pending_empty:
      "Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
        (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
          Scheduler_V611_Parse.xPendingReadyList_') = 0"
    and missed_ticks:
      "Scheduler_V611_Parse.globals.uxMissedTicks_' c = 0"
    and missed_yield:
      "Scheduler_V611_Parse.globals.xMissedYield_' c = 0"
    and current_tasks:
      "Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c = 2"
  shows
    "Scheduler_V611_Delay_Translation.xTaskResumeAll' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result 0 \<and> t = p2_resume_quiet_state c
     \<rbrace>"
  unfolding Scheduler_V611_Delay_Translation.xTaskResumeAll'_def
    Scheduler_V611_Tick_Translation.eal6_port_enter_critical'_def
    Scheduler_V611_Tick_Translation.eal6_port_exit_critical'_def
    Scheduler_V611_Delay_Translation.eal6_port_yield'_def
    vTaskIncrementTick'_def
    p2_resume_quiet_state_def
  apply runs_to_vcg
  apply (simp_all add: suspended depth interrupts pending_guard
      pending_empty missed_ticks missed_yield current_tasks h_val_heap_update)
  apply (subst runs_to_whileLoop_cond_fail)
   apply simp
  apply runs_to_vcg
  apply (simp_all add: suspended depth interrupts pending_guard
      pending_empty missed_ticks missed_yield current_tasks h_val_heap_update)
  done

end
