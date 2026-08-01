theory Scheduler_V611_Delay_Translation
  imports "EAL6_FreeRTOS_V611_Scheduler_Tick.Scheduler_V611_Tick_Translation"
begin

text \<open>
  Second translation rung.  Every previously untranslated operational callee
  of vTaskDelay is in scope.  The two list initialisers are included so later
  invariant proofs have a translated construction path, even though the delay
  operation itself does not call them.
\<close>

autocorres [
  skip_heap_abs,
  scope =
    eal6_port_yield
    vListInitialise
    vListInitialiseItem
    vListInsertEnd
    vListInsert
    vListRemove
    vTaskSuspendAll
    vTaskIncrementTick
    xTaskResumeAll
    vTaskDelay,
  ts_rules = nondet
] "scheduler_translation_unit.c"

print_statement eal6_port_yield'_def
print_statement vTaskSuspendAll'_def
print_statement vTaskIncrementTick'_def
print_statement xTaskResumeAll'_def
print_statement vTaskDelay'_def

end
