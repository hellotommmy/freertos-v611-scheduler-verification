theory Scheduler_Resume_Missed_Tick_Replay
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Yield_Interface.Scheduler_Resume_Missed_Tick_Replay_Yield_Interface"
begin

text \<open>
  Compatibility facade for the complete missed-tick replay relation ladder.
  The declaration order and theorem inventory are preserved in the parent
  sessions; importing this original theory name exposes the full checked
  namespace without replaying every proof in one timeout-bounded session.
\<close>

end
