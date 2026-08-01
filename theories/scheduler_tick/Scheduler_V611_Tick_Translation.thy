theory Scheduler_V611_Tick_Translation
  imports "EAL6_FreeRTOS_V611_Scheduler_Parse.Scheduler_V611_Parse"
begin

text \<open>
  First translation needle.  The scope explicitly includes both reachable
  proof-port bodies; no direct callee is left as a generated SIMPL wrapper.
\<close>

autocorres [
  skip_heap_abs,
  scope =
    eal6_port_enter_critical
    eal6_port_exit_critical
    xTaskGetTickCount,
  ts_rules = nondet
] "scheduler_translation_unit.c"

print_statement eal6_port_enter_critical'_def
print_statement eal6_port_exit_critical'_def
print_statement xTaskGetTickCount'_def

end
