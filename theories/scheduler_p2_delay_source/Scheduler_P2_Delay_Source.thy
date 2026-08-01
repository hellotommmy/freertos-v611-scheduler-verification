theory Scheduler_P2_Delay_Source
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Control_Leaves.Scheduler_P2_Control_Leaves"
begin

text \<open>
  Exact real-source execution of the frozen P2 delay path.  All callees have
  full scheduler-state contracts; this theory opens only the generated
  vTaskDelay body and composes those contracts through its scalar control
  flow and its single nested wake-key write.
\<close>

definition p2_delay_2_source_state ::
  "Scheduler_V611_Parse.globals \<Rightarrow>
   p2_tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow>
   Scheduler_V611_Parse.globals"
where
  "p2_delay_2_source_state c D R =
     p2_yield_state
       (p2_resume_quiet_state
         (scheduler_mem_state
           (p2_remove_wake_insert_heap
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) D R)
           (p2_suspend_state c)))"

lemma p2_generated_wake_key_write_mem_state:
  "Scheduler_V611_Parse.globals.t_hrs_'_update
      (hrs_mem_update
        (heap_update
          (scheduler_generic_item_key_ptr (sd_tcb_ptr D P2_RUN))
          ((5 :: 32 word) + 2)))
      (scheduler_mem_state
        (raw_remove_concrete_heap h
          (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))) c) =
   scheduler_mem_state (p2_remove_then_wake_heap h D) c"
  by (simp add:
      scheduler_heap_modify_as_mem_state
      p2_remove_then_wake_heap_def
      p2_wake_key_heap_def
      scheduler_generic_item_key_heap_def)

theorem scheduler_vTaskDelay_2_p2_exact_state:
  fixes c :: Scheduler_V611_Parse.globals
  assumes endpoint:
      "scheduler_endpoint_rel StableRunning D R c p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
  shows
    "Scheduler_V611_Delay_Translation.vTaskDelay' (2 :: 32 word) \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = p2_delay_2_source_state c D R
     \<rbrace>"
proof -
  let ?h0 = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?tp = "sd_tcb_ptr D P2_RUN"
  let ?sp = "scheduler_generic_item_ptr ?tp"
  let ?rp = "abi_generic_list_item_ptr ?tp"
  let ?hr = "raw_remove_concrete_heap ?h0 ?rp"
  let ?hk = "p2_remove_then_wake_heap ?h0 D"
  let ?hf = "p2_remove_wake_insert_heap ?h0 D R"
  let ?cs = "p2_suspend_state c"
  let ?cr = "scheduler_mem_state ?hr ?cs"
  let ?ck = "scheduler_mem_state ?hk ?cs"
  let ?ci = "scheduler_mem_state ?hf ?cs"
  let ?cq = "p2_resume_quiet_state ?ci"

  have raw: "raw_scheduler_rel D R c p2_pre"
    using endpoint by simp
  have decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R c p2_pre"
    and roles: "scheduler_role_rel R c p2_pre"
    and scalars: "scheduler_scalar_rel c p2_pre"
    and current: "scheduler_current_rel D c p2_pre"
    and boundary: "scheduler_boundary_rel c"
    using raw by (auto simp: raw_scheduler_rel_def)

  have current_tcb:
      "Scheduler_V611_Parse.globals.pxCurrentTCB_' c = ?tp"
    using current
    by (simp add: scheduler_current_rel_def p2_pre_def)
  have delayed_root:
      "Scheduler_V611_Parse.globals.pxDelayedTaskList_' c =
       sr_delayed_a R"
    using roles
    by (simp add: scheduler_role_rel_def p2_pre_def)

  have tick: "Scheduler_V611_Parse.globals.xTickCount_' c = 5"
    and suspended_u:
      "unat (Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c) = 0"
    and missed_ticks_u:
      "unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) = 0"
    and missed_yield0:
      "Scheduler_V611_Parse.globals.xMissedYield_' c = 0"
    and current_tasks_u:
      "unat
        (Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c) = 2"
    using scalars
    by (simp_all add: scheduler_scalar_rel_def p2_pre_def)

  have suspended0:
      "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c = 0"
    using suspended_u by (simp add: unat_eq_0)
  have missed_ticks0:
      "Scheduler_V611_Parse.globals.uxMissedTicks_' c = 0"
    using missed_ticks_u by (simp add: unat_eq_0)
  have current_tasks2:
      "Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c = 2"
    using current_tasks_u by (simp add: word_unat_eq_iff)

  have depth0:
      "Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c = 0"
    and interrupts0:
      "Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' c = 0"
    using boundary by (auto simp: scheduler_boundary_rel_def)

  from p2_source_footprint_run_guardsD[OF footprint]
  have tcb_guard: "c_guard ?tp"
    and item_guard: "c_guard ?sp"
    by blast+

  have pending_guard:
      "c_guard Scheduler_V611_Parse.xPendingReadyList_'"
    by (rule p2_pending_ready_guard[OF footprint])

  have item_addr:
      "PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
         &(?tp\<rightarrow>[''xGenericListItem_C'']) = ?sp"
    by (simp add: scheduler_generic_item_ptr_def)

  have key_addr:
      "PTR(32 word)
         &(?tp\<rightarrow>[''xGenericListItem_C'', ''xItemValue_C'']) =
       scheduler_generic_item_key_ptr ?tp"
    by (simp add: scheduler_generic_item_key_ptr_def)

  have lists_cs: "scheduler_lists_rel D R ?cs p2_pre"
    using lists
    by (simp add: scheduler_lists_rel_def p2_suspend_state_def)

  have current_cs:
      "Scheduler_V611_Parse.globals.pxCurrentTCB_' ?cs = ?tp"
    and current_cr:
      "Scheduler_V611_Parse.globals.pxCurrentTCB_' ?cr = ?tp"
    and current_ck:
      "Scheduler_V611_Parse.globals.pxCurrentTCB_' ?ck = ?tp"
    using current_tcb
    by (simp_all add: p2_suspend_state_def scheduler_mem_state_def)

  have tick_cs:
      "Scheduler_V611_Parse.globals.xTickCount_' ?cs = 5"
    and tick_cr:
      "Scheduler_V611_Parse.globals.xTickCount_' ?cr = 5"
    and tick_ck:
      "Scheduler_V611_Parse.globals.xTickCount_' ?ck = 5"
    using tick
    by (simp_all add: p2_suspend_state_def scheduler_mem_state_def)

  have delayed_cr:
      "Scheduler_V611_Parse.globals.pxDelayedTaskList_' ?cr =
       sr_delayed_a R"
    using delayed_root
    by (simp add: p2_suspend_state_def scheduler_mem_state_def)

  have delayed_ck:
      "Scheduler_V611_Parse.globals.pxDelayedTaskList_' ?ck =
       sr_delayed_a R"
    using delayed_root
    by (simp add: p2_suspend_state_def scheduler_mem_state_def)

  note suspend_exact = scheduler_vTaskSuspendAll_exact[where c=c]

  have remove_exact:
      "Scheduler_V611_Delay_Translation.vListRemove' ?sp \<bullet> ?cs
       \<lbrace>\<lambda>r t. r = Result () \<and> t = ?cr\<rbrace>"
  proof -
    note remove0 =
      scheduler_vListRemove_p2_ready2_exact_state[
        where s="?cs" and D=D and R=R, OF decode lists_cs]
    show ?thesis
      using remove0
      by (simp add: p2_suspend_state_def)
  qed

  have key_modify:
      "Scheduler_V611_Parse.globals.t_hrs_'_update
         (hrs_mem_update
           (heap_update
             (PTR(32 word)
               &(?tp\<rightarrow>[''xGenericListItem_C'',
                              ''xItemValue_C'']))
             (7 :: 32 word)))
         ?cr = ?ck"
    using p2_generated_wake_key_write_mem_state[
      where h="?h0" and D=D and c="?cs"] key_addr
    by simp

  have key_modify_scheduler:
      "Scheduler_V611_Parse.globals.t_hrs_'_update
         (hrs_mem_update
           (heap_update (scheduler_generic_item_key_ptr ?tp)
             (7 :: 32 word))) ?cr = ?ck"
    using p2_generated_wake_key_write_mem_state[
      where h="?h0" and D=D and c="?cs"]
    by simp

  have heap_ck:
      "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?ck) = ?hk"
    by simp

  have wake_not_overflow_cr:
      "\<not> ((7 :: 32 word) <
        Scheduler_V611_Parse.globals.xTickCount_' ?cr)"
    using tick_cr by simp

  have insert_exact:
      "Scheduler_V611_Delay_Translation.vListInsert'
         (sr_delayed_a R) ?sp \<bullet> ?ck
       \<lbrace>\<lambda>r t. r = Result () \<and> t = ?ci\<rbrace>"
  proof -
    have insert0:
        "Scheduler_V611_Delay_Translation.vListInsert'
           (sr_delayed_a R) ?sp \<bullet> ?ck
         \<lbrace>\<lambda>r t.
           r = Result () \<and>
           t = scheduler_mem_state
             (raw_ordered_insert_empty_heap ?hk
               (abi_list_ptr (sr_delayed_a R)) ?rp) ?ck
         \<rbrace>"
      by (rule
          scheduler_vListInsert_p2_delayed_a_after_remove_wake_exact_state[
            OF decode lists footprint heap_ck])
    show ?thesis
      using insert0
      by (simp add: p2_remove_wake_insert_heap_def)
  qed

  have suspended_i:
      "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' ?ci = 1"
    using suspended0
    by (simp add: p2_suspend_state_def scheduler_mem_state_def)
  have depth_i:
      "Scheduler_V611_Parse.globals.eal6_port_critical_depth_' ?ci = 0"
    using depth0
    by (simp add: p2_suspend_state_def scheduler_mem_state_def)
  have interrupts_i:
      "Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' ?ci = 0"
    using interrupts0
    by (simp add: p2_suspend_state_def scheduler_mem_state_def)
  have missed_ticks_i:
      "Scheduler_V611_Parse.globals.uxMissedTicks_' ?ci = 0"
    using missed_ticks0
    by (simp add: p2_suspend_state_def scheduler_mem_state_def)
  have missed_yield_i:
      "Scheduler_V611_Parse.globals.xMissedYield_' ?ci = 0"
    using missed_yield0
    by (simp add: p2_suspend_state_def scheduler_mem_state_def)
  have current_tasks_i:
      "Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' ?ci = 2"
    using current_tasks2
    by (simp add: p2_suspend_state_def scheduler_mem_state_def)

  have pending_i:
      "Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
         (h_val
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?ci))
           Scheduler_V611_Parse.xPendingReadyList_') = 0"
  proof -
    note pending0 =
      p2_remove_wake_insert_pending_scheduler_count_zero[
        where s=c and D=D and R=R, OF decode lists footprint]
    show ?thesis using pending0 by simp
  qed

  note resume_exact =
    scheduler_xTaskResumeAll_quiet_exact[
      where c="?ci",
      OF suspended_i depth_i interrupts_i pending_guard pending_i
         missed_ticks_i missed_yield_i current_tasks_i]

  note yield_exact = scheduler_eal6_port_yield_exact[where c="?cq"]

  show ?thesis
  supply current_cs[simp] current_cr[simp] current_ck[simp]
    tick_cs[simp] tick_cr[simp] tick_ck[simp]
    delayed_cr[simp] delayed_ck[simp]
    item_addr[simp] key_addr[simp] key_modify[simp]
    tcb_guard[simp] item_guard[simp]

  unfolding Scheduler_V611_Delay_Translation.vTaskDelay'_def
  apply runs_to_vcg
  apply simp_all
  apply (rule runs_to_weaken[OF suspend_exact])
  apply clarsimp

  apply runs_to_vcg
  apply (rule runs_to_weaken[OF remove_exact])
  apply clarsimp

  apply runs_to_vcg
  apply (simp only: key_modify_scheduler)
  apply (rule runs_to_weaken[OF insert_exact])
  apply clarsimp

  apply runs_to_vcg
  apply (rule runs_to_weaken[OF resume_exact])
  apply clarsimp

  apply runs_to_vcg
  apply (rule runs_to_weaken[OF yield_exact])
  apply (simp add: p2_delay_2_source_state_def)
  done
qed

end
