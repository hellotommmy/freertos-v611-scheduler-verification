theory Scheduler_P2_Generated_Layout_First
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Roots.Scheduler_V611_Roots_Translation"
    "EAL6_FreeRTOS_V611_List_Raw_R5_Relation.List_V611_Raw_R5_Relation"
begin

text \<open>
  This leaf only exposes generated scheduler declarations and the first
  cross-translation-unit type diagnostic.  It proves no footprint theorem.
\<close>

(* Exact scheduler TCB selector types. *)
term "xGenericListItem_C"
term "xEventListItem_C"
term "uxPriority_C"

(* Exact embedded addresses and heap read. *)
term "(\<lambda>tp :: tskTaskControlBlock_C ptr.
  PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
    &(tp\<rightarrow>[''xGenericListItem_C'']))"
term "(\<lambda>tp :: tskTaskControlBlock_C ptr.
  PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
    &(tp\<rightarrow>[''xEventListItem_C'']))"
term "(\<lambda>(c :: Scheduler_V611_Parse.globals)
          (tp :: tskTaskControlBlock_C ptr).
  uxPriority_C
    (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) tp))"

(* Generated TCB field layout and size facts. *)
print_statement tskTaskControlBlock_C_xGenericListItem_C_fl
print_statement tskTaskControlBlock_C_xEventListItem_C_fl
print_statement tskTaskControlBlock_C_uxPriority_C_fl
print_statement tskTaskControlBlock_C_size

(* Addressed roots and ready element constructor. *)
term "Scheduler_V611_Parse.pxReadyTasksLists_'"
term "(\<lambda>p :: nat.
  array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_' False p)"
term "Scheduler_V611_Parse.xDelayedTaskList1_'"
term "Scheduler_V611_Parse.xDelayedTaskList2_'"
term "Scheduler_V611_Parse.xPendingReadyList_'"
term "Scheduler_V611_Parse.xSuspendedTaskList_'"
print_locale scheduler_translation_unit_global_addresses
print_statement scheduler_translation_unit_global_addresses.all_distinct

(* State/role selectors and proof-port observables. *)
term "(\<lambda>c :: Scheduler_V611_Parse.globals.
  (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c,
   Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_' c,
   Scheduler_V611_Parse.globals.pxCurrentTCB_' c))"
term "(\<lambda>c :: Scheduler_V611_Parse.globals.
  (Scheduler_V611_Parse.globals.xTickCount_' c,
   Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c,
   Scheduler_V611_Parse.globals.uxTopReadyPriority_' c,
   Scheduler_V611_Parse.globals.uxMissedTicks_' c,
   Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c,
   Scheduler_V611_Parse.globals.eal6_port_yield_count_' c,
   Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c,
   Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' c))"
term "(\<lambda>c :: Scheduler_V611_Parse.globals.
  (Scheduler_V611_Parse.globals.xMissedYield_' c,
   Scheduler_V611_Parse.globals.xNumOfOverflows_' c,
   Scheduler_V611_Parse.globals.xSchedulerRunning_' c))"

(* Source definitions that pin all non-layout spellings used by P2. *)
print_statement vTaskDelay'_def
print_statement xTaskResumeAll'_def
print_statement vTaskIncrementTick'_def
print_statement vTaskSwitchContext'_def

(* The byte-heap carrier is checked independently of generated struct types. *)
term "(\<lambda>(c :: Scheduler_V611_Parse.globals) lp xs.
  raw_xlist_rel
    (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) lp xs)"

(* The generated struct universes are printed separately: they are distinct. *)
term "raw_xlist_rel"
term "(undefined :: List_V611_Raw_Skip_Translation.xLIST_C ptr)"
term "(undefined :: Scheduler_V611_Parse.xLIST_C ptr)"
term "(undefined :: List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr)"
term "(undefined :: Scheduler_V611_Parse.xLIST_ITEM_C ptr)"

end
