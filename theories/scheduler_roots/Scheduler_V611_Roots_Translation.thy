theory Scheduler_V611_Roots_Translation
  imports "EAL6_FreeRTOS_V611_Scheduler_Delay.Scheduler_V611_Delay_Translation"
begin

text \<open>
  Final frozen-root translation rung.  Its two new roots call only functions
  translated by the parent rungs or expand configuration-active list macros.
\<close>

autocorres [
  skip_heap_abs,
  scope =
    vTaskDelayUntil
    vTaskSwitchContext,
  ts_rules = nondet
] "scheduler_translation_unit.c"

print_statement vTaskDelayUntil'_def
print_statement vTaskSwitchContext'_def

end
