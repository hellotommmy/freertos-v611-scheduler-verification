theory Scheduler_One_Due_Task_Phases_Tail_Insert
  imports
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Priority_Frame.Scheduler_One_Due_Task_Phases_Priority_Frame"
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Generated.Scheduler_One_Due_Task_Phases_Generated"
    "EAL6_FreeRTOS_V611_Scheduler_Insert_End_Translation_General.Scheduler_Insert_End_Translation_General"
begin

text \<open>
  Composition of the generated top/ready tail through the ready insertion.
  From the state after both removals the top-raise conditional reads the
  preserved priority, the in-range guard discharges from the observation
  bound, the ready selection returns exactly the gate's target root, and
  the generated \<open>vListInsertEnd'\<close> produces the exact insert heap over
  the after-event target ring.  The delayed-head remainder -- the read
  that feeds the next loop iteration -- is a named factor handed to a
  continuation triple at that exact state.  No task, priority, tick,
  ring population or heap layout is fixed.
\<close>

definition one_due_tick_delayed_remainder ::
  "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr,
     Scheduler_V611_Parse.globals) spec_monad"
where
  "one_due_tick_delayed_remainder = do {
     guard
       (\<lambda>s. c_guard
         (Scheduler_V611_Parse.globals.pxDelayedTaskList_' s));
     ret \<leftarrow> condition
       (\<lambda>s. Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
          (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
            (Scheduler_V611_Parse.globals.pxDelayedTaskList_' s)) \<noteq> 0)
       (do {
         guard
           (\<lambda>s. c_guard
             (Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxNext_C
               (Scheduler_V611_Parse.xLIST_C.xListEnd_C
                 (h_val
                   (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
                   (Scheduler_V611_Parse.globals.pxDelayedTaskList_' s)))));
         guard
           (\<lambda>s. c_guard
             (PTR(Scheduler_V611_Parse.xMINI_LIST_ITEM_C)
               &(Scheduler_V611_Parse.globals.pxDelayedTaskList_' s
                 \<rightarrow>[''xListEnd_C''])));
         gets
           (\<lambda>s. Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
             (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
               (Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxNext_C
                 (Scheduler_V611_Parse.xLIST_C.xListEnd_C
                   (h_val
                     (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
                     (Scheduler_V611_Parse.globals.pxDelayedTaskList_'
                       s))))))
       })
       (return NULL);
     return
       (PTR_COERCE(unit \<rightarrow>
          Scheduler_V611_Parse.tskTaskControlBlock_C) ret)
   }"

lemma one_due_tail_source_split:
  "one_due_tick_top_ready_tail_source pxTCB = do {
     condition
       (\<lambda>s. Scheduler_V611_Parse.globals.uxTopReadyPriority_' s <
          Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
            (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
              pxTCB))
       (modify
         (\<lambda>s. s\<lparr>Scheduler_V611_Parse.globals.uxTopReadyPriority_' :=
           Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
             (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
               pxTCB)\<rparr>))
       skip;
     guard
       (\<lambda>s. Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
          (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
            pxTCB) < 4);
     guard (\<lambda>_. c_guard Scheduler_V611_Parse.pxReadyTasksLists_');
     pxList \<leftarrow> gets
       (\<lambda>s. array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_'
          False
          (unat
            (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
              (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
                pxTCB))));
     ret \<leftarrow> Scheduler_V611_Delay_Translation.vListInsertEnd'
       pxList (scheduler_generic_item_ptr pxTCB);
     one_due_tick_delayed_remainder
   }"
  by (simp add: one_due_tick_top_ready_tail_source_def
      one_due_tick_delayed_remainder_def)

lemma one_due_ready_array_guard:
  "c_guard Scheduler_V611_Parse.pxReadyTasksLists_'"
proof -
  have no_wrap:
    "unat (0x00102020 :: addr) + 80 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have membership:
    "((0 :: addr) \<in> {(0x00102020 :: addr)..+80}) =
      (unat (0x00102020 :: addr) \<le> unat (0 :: addr) \<and>
       unat (0 :: addr) < unat (0x00102020 :: addr) + 80)"
    by (rule intvl_no_overflow_nat[OF no_wrap])
  have no_null: "(0 :: addr) \<notin> {(0x00102020 :: addr)..+80}"
    using membership by simp
  show ?thesis
    unfolding Scheduler_V611_Parse.pxReadyTasksLists_'_def
    using no_null
    by (simp add: c_guard_def c_null_guard_def ptr_aligned_def
        align_of_def align_td_array size_of_def size_td_array)
qed

lemma one_due_gateH_task_observationD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a"
  using rel
  unfolding one_due_gateH_entry_rel_def Let_def
  by blast

lemma one_due_gateH_live_absD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows "odc_live C = sa_live a"
  using rel
  unfolding one_due_gateH_entry_rel_def Let_def
  by blast

theorem one_due_tick_tail_insert_composed:
  fixes Q
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
    and cont:
      "\<And>t. hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t) =
           one_due_ready_insert_heap D C generic_raw
             (one_due_event_remove_heap D C branch
               (one_due_generic_remove_heap D C
                 (hrs_mem
                   (Scheduler_V611_Parse.globals.t_hrs_' c)))) \<Longrightarrow>
         Scheduler_V611_Parse.globals.pxDelayedTaskList_' t =
           Scheduler_V611_Parse.globals.pxDelayedTaskList_' c \<Longrightarrow>
         Scheduler_V611_Parse.globals.uxTopReadyPriority_' t =
           (if Scheduler_V611_Parse.globals.uxTopReadyPriority_' c <
              Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
                (h_val
                  (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
                  (sd_tcb_ptr D (odc_task C)))
            then
              Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
                (h_val
                  (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
                  (sd_tcb_ptr D (odc_task C)))
            else
              Scheduler_V611_Parse.globals.uxTopReadyPriority_' c)
           \<Longrightarrow>
         Scheduler_V611_Parse.globals.xTickCount_' t =
           Scheduler_V611_Parse.globals.xTickCount_' c \<Longrightarrow>
         one_due_tick_delayed_remainder \<bullet> t \<lbrace>Q\<rbrace>"
  shows
    "one_due_tick_top_ready_tail_source (sd_tcb_ptr D (odc_task C)) \<bullet>
       (scheduler_mem_state
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
         c)
     \<lbrace>Q\<rbrace>"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?he = "one_due_event_remove_heap D C branch
    (one_due_generic_remove_heap D C ?h)"
  let ?tp = "sd_tcb_ptr D (odc_task C)"
  let ?target = "one_due_target_root C"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  have task_live: "odc_task C \<in> odc_live C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have live_abs: "odc_task C \<in> sa_live a"
    using task_live one_due_gateH_live_absD[OF rel] by simp
  have pri_he:
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val ?he ?tp) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val ?h ?tp)"
    by (rule one_due_gateH_priority_after_eventD[OF rel task_live])
  have pri_lt:
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val ?h ?tp) < 4"
    using one_due_gateH_task_observationD[OF rel] live_abs
    by (simp add: TaskObservationRel_def)
  have target_sel:
    "?target =
       abi_list_ptr
         (array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_'
           False
           (unat
             (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
               (h_val ?h ?tp))))"
    by (rule one_due_gateH_source_ready_selectionD[OF rel roots])
  note after_event = one_due_gateH_after_event_obligations[OF rel]
  have rel_he_target:
    "raw_xlist_rel ?he ?target (generic_raw ?target)"
    using after_event
    by (simp add: one_due_after_event_obligations_def Let_def)
  have fresh:
    "raw_fresh_for_insert ?target (ring (generic_raw ?target)) ?p"
    using after_event
    by (simp add: one_due_after_event_obligations_def Let_def)
  have hrs_reduce:
    "hrs_mem (hrs_mem_update (\<lambda>_. X) Y) = X" for X Y
    by (simp add: hrs_mem_update_def hrs_mem_def split: prod.splits)
  have item_abi:
    "abi_item_ptr (scheduler_generic_item_ptr ?tp) = ?p"
    by (simp add: one_due_generic_raw_ptr_def)
  show ?thesis
    apply (subst one_due_tail_source_split)
    apply runs_to_vcg
    subgoal by (simp add: pri_he pri_lt)
    subgoal by (rule one_due_ready_array_guard)
    subgoal
      apply (rule runs_to_weaken
          [OF scheduler_vListInsertEnd_general_exact_state])
        apply (insert rel_he_target)
        apply (simp add: scheduler_mem_state_def hrs_reduce pri_he
          target_sel[symmetric])
       apply (insert fresh)
       apply (simp add: item_abi pri_he target_sel[symmetric]
         one_due_generic_raw_ptr_def)
      apply (clarsimp split: exception_or_result_splits)
      apply (rule cont)
         apply (simp add: scheduler_mem_state_def hrs_reduce pri_he
           target_sel[symmetric] item_abi
           one_due_generic_raw_ptr_def
           one_due_ready_insert_heap_def)
        apply (simp add: scheduler_mem_state_def)
       apply (simp add: scheduler_mem_state_def pri_he)
      apply (simp add: scheduler_mem_state_def)
      done
    subgoal by (simp add: pri_he pri_lt)
    subgoal by (rule one_due_ready_array_guard)
    subgoal
      apply (rule runs_to_weaken
          [OF scheduler_vListInsertEnd_general_exact_state])
        apply (insert rel_he_target)
        apply (simp add: scheduler_mem_state_def hrs_reduce pri_he
          target_sel[symmetric])
       apply (insert fresh)
       apply (simp add: item_abi pri_he target_sel[symmetric]
         one_due_generic_raw_ptr_def)
      apply (clarsimp split: exception_or_result_splits)
      apply (rule cont)
         apply (simp add: scheduler_mem_state_def hrs_reduce pri_he
           target_sel[symmetric] item_abi
           one_due_generic_raw_ptr_def
           one_due_ready_insert_heap_def)
        apply (simp add: scheduler_mem_state_def)
       apply (simp add: scheduler_mem_state_def pri_he)
      apply (simp add: scheduler_mem_state_def)
      done
    done
qed

end
