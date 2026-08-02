theory Scheduler_Concurrent_Contract_Interface
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Concurrent_Cutpoint.Scheduler_Concurrent_Cutpoint"
begin

text \<open>
  Compatibility facade for the bounded-build concurrent contract staircase.
  All declarations retain their original base names; the state, environment,
  program, interleaving, and representation layers live in separate parent
  sessions so each active proof cursor can replay within the 120-second gate.
\<close>

end
