theory Scheduler_V611_Delay_Until_No_Delay_Refinement
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delay_Zero_Refinement.Scheduler_V611_Delay_Zero_Refinement"
begin

text \<open>
  Restricted vTaskDelayUntil leaf.  The API is entered while the scheduler is
  already suspended once, so its internal suspend/resume pair changes the
  concrete depth 1 -> 2 -> 1 and xTaskResumeAll cannot enter pending-ready or
  missed-tick processing.  The chosen arithmetic branch commits the nominal
  wake time but does not block the current task.  The final explicit yield is
  still observable.
\<close>

definition scheduler_delay_until_no_delay_state ::
  "globals \<Rightarrow> 32 word ptr \<Rightarrow> 32 word \<Rightarrow> globals"
where
  "scheduler_delay_until_no_delay_state c previous_ptr increment =
     (let previous = h_val (hrs_mem (t_hrs_' c)) previous_ptr;
          wake = previous + increment;
          c1 = t_hrs_'_update
                 (hrs_mem_update (heap_update previous_ptr wake)) c
      in eal6_port_yield_count_'_update (\<lambda>n. n + 1) c1)"

theorem vTaskDelayUntil_suspended_no_delay_result:
  assumes guard: "c_guard previous_ptr"
      and suspended: "uxSchedulerSuspended_' c = 1"
      and depth: "eal6_port_critical_depth_' c = 0"
      and interrupts: "eal6_port_interrupts_disabled_' c = 0"
      and no_delay:
        "\<not> should_delay_until (xTickCount_' c)
           (h_val (hrs_mem (t_hrs_' c)) previous_ptr)
           (h_val (hrs_mem (t_hrs_' c)) previous_ptr + increment)"
  shows
    "vTaskDelayUntil' previous_ptr increment \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_delay_until_no_delay_state c previous_ptr increment
     \<rbrace>"
proof -
  let ?previous = "h_val (hrs_mem (t_hrs_' c)) previous_ptr"
  let ?wake = "?previous + increment"
  have overflow_branch:
    "xTickCount_' c < ?previous \<Longrightarrow>
     \<not> (?wake < ?previous \<and> xTickCount_' c < ?wake)"
    using no_delay by (simp add: should_delay_until_def)
  have ordinary_branch:
    "\<not> xTickCount_' c < ?previous \<Longrightarrow>
     \<not> (?wake < ?previous \<or> xTickCount_' c < ?wake)"
    using no_delay by (simp add: should_delay_until_def)
  show ?thesis
    unfolding vTaskDelayUntil'_def vTaskSuspendAll'_def xTaskResumeAll'_def
      eal6_port_enter_critical'_def eal6_port_exit_critical'_def
      eal6_port_yield'_def scheduler_delay_until_no_delay_state_def
    apply runs_to_vcg
    apply (simp_all add: guard suspended depth interrupts Let_def)
    apply (all \<open>insert no_delay\<close>)
    apply (all \<open>simp add: should_delay_until_def\<close>)
    done
qed

lemma scheduler_control_rel_delay_until_no_delay_state:
  assumes rel: "scheduler_control_rel c a"
      and no_wrap: "scheduler_yield_count_no_wrap c"
  shows
    "scheduler_control_rel
       (scheduler_delay_until_no_delay_state c previous_ptr increment)
       (a\<lparr>sa_yield_count := Suc (sa_yield_count a)\<rparr>)"
proof -
  have step:
    "unat (eal6_port_yield_count_' c + 1) =
       Suc (unat (eal6_port_yield_count_' c))"
    using yield_count_unat_add_one[OF no_wrap] .
  show ?thesis
    using rel step
    by (simp add: scheduler_control_rel_def
        scheduler_delay_until_no_delay_state_def Let_def)
qed

theorem vTaskDelayUntil_suspended_no_delay_refines:
  assumes rel: "scheduler_control_rel c a"
      and guard: "c_guard previous_ptr"
      and suspended: "uxSchedulerSuspended_' c = 1"
      and depth: "eal6_port_critical_depth_' c = 0"
      and interrupts: "eal6_port_interrupts_disabled_' c = 0"
      and no_delay:
        "\<not> should_delay_until (xTickCount_' c)
           (h_val (hrs_mem (t_hrs_' c)) previous_ptr)
           (h_val (hrs_mem (t_hrs_' c)) previous_ptr + increment)"
      and no_wrap: "scheduler_yield_count_no_wrap c"
  shows
    "vTaskDelayUntil' previous_ptr increment \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       h_val (hrs_mem (t_hrs_' t)) previous_ptr =
         fst (task_delay_until_abs
           (h_val (hrs_mem (t_hrs_' c)) previous_ptr) increment a) \<and>
       scheduler_control_rel t
         (snd (task_delay_until_abs
           (h_val (hrs_mem (t_hrs_' c)) previous_ptr) increment a))
     \<rbrace>"
proof -
  let ?previous = "h_val (hrs_mem (t_hrs_' c)) previous_ptr"
  let ?wake = "?previous + increment"
  have abstract_step:
    "task_delay_until_abs ?previous increment a =
       (?wake, a\<lparr>sa_yield_count := Suc (sa_yield_count a)\<rparr>)"
    using no_delay rel
    by (simp add: scheduler_control_rel_def task_delay_until_abs_def
        request_yield_def Let_def)
  have control:
    "scheduler_control_rel
       (scheduler_delay_until_no_delay_state c previous_ptr increment)
       (a\<lparr>sa_yield_count := Suc (sa_yield_count a)\<rparr>)"
    by (rule scheduler_control_rel_delay_until_no_delay_state[OF rel no_wrap])
  have wake_readback:
    "h_val
       (hrs_mem
         (t_hrs_'
           (scheduler_delay_until_no_delay_state c previous_ptr increment)))
       previous_ptr = ?wake"
    using guard
    by (simp add: scheduler_delay_until_no_delay_state_def
        hrs_mem_update h_val_heap_update Let_def)
  note exact = vTaskDelayUntil_suspended_no_delay_result[
    OF guard suspended depth interrupts no_delay]
  show ?thesis
    apply (rule runs_to_weaken[OF exact])
    using abstract_step control wake_readback
    by auto
qed

end
