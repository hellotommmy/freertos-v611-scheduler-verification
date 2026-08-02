theory Scheduler_Resume_Missed_Tick_Replay_Pending_Join
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Yield_OR.Scheduler_Resume_Missed_Tick_Replay_Yield_OR"
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Phases.Scheduler_Resume_Pending_Drain_Phases"
begin

text \<open>
  Pending-drain interface.  All task identities, root families, priority/key
  functions and the processed prefix remain parameters of C, S and done.  The
  established pending-prefix theorem supplies exactly the first disjunct of
  the missed-tick/final-yield accumulator.
\<close>

definition missed_tick_entry_after_pending ::
  "('tid, 'root) resume_pending_context \<Rightarrow> 'tid list \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 32 word \<Rightarrow>
   'tid missed_tick_replay_state"
where
  "missed_tick_entry_after_pending C done S s w =
     missed_tick_replay_entry s w
       (rps_local_yield (resume_pending_process_prefix C done S))"

theorem missed_tick_entry_after_pending_yield:
  "mtrs_yield_required (missed_tick_entry_after_pending C done S s w)
   \<longleftrightarrow>
   rps_local_yield S \<or>
     (\<exists>t\<in>set done.
        rpc_current_priority C \<le> rpc_priority C t)"
proof -
  have entry_yield:
    "mtrs_yield_required (missed_tick_entry_after_pending C done S s w) =
       rps_local_yield (resume_pending_process_prefix C done S)"
    by (simp only: missed_tick_entry_after_pending_def
        missed_tick_replay_entry_def
        missed_tick_replay_state.select_convs)
  have prefix:
    "rps_local_yield (resume_pending_process_prefix C done S) \<longleftrightarrow>
       rps_local_yield S \<or>
         (\<exists>t\<in>set done.
           rpc_current_priority C \<le> rpc_priority C t)"
    by (rule resume_pending_process_prefix_local_yield)
  show ?thesis using entry_yield prefix by simp
qed

theorem resume_pending_missed_tick_outer_requested:
  "missed_tick_outer_requested
     (missed_tick_replay_and_mark
       (missed_tick_entry_after_pending C done S s w))
   \<longleftrightarrow>
   rps_local_yield S \<or>
   (\<exists>t\<in>set done.
      rpc_current_priority C \<le> rpc_priority C t) \<or>
   w \<noteq> 0 \<or> sa_missed_yield s"
proof -
  let ?entry = "missed_tick_entry_after_pending C done S s w"
  have sources:
    "missed_tick_outer_requested (missed_tick_replay_and_mark ?entry)
     \<longleftrightarrow>
     mtrs_yield_required ?entry \<or>
     mtrs_remaining ?entry > 0 \<or>
     sa_missed_yield (mtrs_scheduler ?entry)"
    by (rule missed_tick_outer_requested_sources)
  have pending:
    "mtrs_yield_required ?entry \<longleftrightarrow>
     rps_local_yield S \<or>
       (\<exists>t\<in>set done.
         rpc_current_priority C \<le> rpc_priority C t)"
    by (rule missed_tick_entry_after_pending_yield)
  have remaining: "mtrs_remaining ?entry = unat w"
    by (simp only: missed_tick_entry_after_pending_def
        missed_tick_replay_entry_def
        missed_tick_replay_state.select_convs)
  have missed_yield:
    "sa_missed_yield (mtrs_scheduler ?entry) = sa_missed_yield s"
    by (simp add: missed_tick_entry_after_pending_def
        missed_tick_replay_entry_def)
  show ?thesis
    using sources pending remaining missed_yield
    by (simp add: unat_gt_0)
qed

end
