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

end
