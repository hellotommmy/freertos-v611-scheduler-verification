theory Scheduler_Resume_Missed_Tick_Replay_Yield_OR
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Tick_Wrap.Scheduler_Resume_Missed_Tick_Replay_Tick_Wrap"
begin

text \<open>
  Yield aggregation mirrors the two source joins.  The pending drain supplies
  an incoming OR-accumulator.  A nonempty missed-tick debt sets it true only
  after all replay steps (for this build configUSE_PREEMPTION = 1).  The final
  branch ORs that flag with xMissedYield, clears xMissedYield on the true
  branch, and performs exactly one abstract yield regardless of how many
  causes were true.
\<close>

definition missed_tick_mark_replay_yield ::
  "bool \<Rightarrow> 'tid missed_tick_replay_state \<Rightarrow>
   'tid missed_tick_replay_state"
where
  "missed_tick_mark_replay_yield had_debt r =
     r\<lparr>mtrs_yield_required :=
       mtrs_yield_required r \<or> had_debt\<rparr>"

definition missed_tick_replay_and_mark ::
  "'tid missed_tick_replay_state \<Rightarrow>
   'tid missed_tick_replay_state"
where
  "missed_tick_replay_and_mark entry =
     missed_tick_mark_replay_yield
       (mtrs_remaining entry > 0)
       (missed_tick_steps (mtrs_remaining entry) entry)"

definition missed_tick_outer_requested ::
  "'tid missed_tick_replay_state \<Rightarrow> bool"
where
  "missed_tick_outer_requested r \<longleftrightarrow>
     mtrs_yield_required r \<or> sa_missed_yield (mtrs_scheduler r)"

definition missed_tick_outer_finish ::
  "'tid missed_tick_replay_state \<Rightarrow>
   bool \<times> 'tid scheduler_abs"
where
  "missed_tick_outer_finish r =
     (let requested = missed_tick_outer_requested r;
          base = (if requested
                  then (mtrs_scheduler r)\<lparr>sa_missed_yield := False\<rparr>
                  else mtrs_scheduler r)
      in (requested, if requested then request_yield base else base))"

lemma missed_tick_replay_and_mark_count_zero:
  assumes rel: "missed_tick_count_rel entry"
  shows
    "mtrs_source_count (missed_tick_replay_and_mark entry) = 0 \<and>
     sa_missed_ticks
       (mtrs_scheduler (missed_tick_replay_and_mark entry)) = 0"
proof -
  have inv:
    "missed_tick_loop_inv (mtrs_remaining entry)
       (mtrs_remaining entry) 0 entry
       (missed_tick_steps (mtrs_remaining entry) entry)"
    by (rule missed_tick_loop_inv_at_any_split[OF rel]) simp_all
  note exit = missed_tick_loop_zero_exit[OF inv]
  show ?thesis
    using exit by (simp add: missed_tick_replay_and_mark_def
        missed_tick_mark_replay_yield_def)
qed

lemma missed_tick_replay_and_mark_yield:
  "mtrs_yield_required (missed_tick_replay_and_mark entry) \<longleftrightarrow>
   mtrs_yield_required entry \<or> mtrs_remaining entry > 0"
  by (simp add: missed_tick_replay_and_mark_def
      missed_tick_mark_replay_yield_def)

theorem missed_tick_outer_single_yield:
  fixes r :: "'tid missed_tick_replay_state"
  defines "requested \<equiv> missed_tick_outer_requested r"
  defines "result \<equiv> missed_tick_outer_finish r"
  shows
    "fst result = requested \<and>
     sa_missed_yield (snd result) = False \<and>
     sa_yield_count (snd result) =
       sa_yield_count (mtrs_scheduler r) + (if requested then 1 else 0)"
  unfolding requested_def result_def missed_tick_outer_finish_def
    missed_tick_outer_requested_def request_yield_def Let_def
  by auto

theorem missed_tick_outer_requested_sources:
  "missed_tick_outer_requested (missed_tick_replay_and_mark entry)
   \<longleftrightarrow>
   mtrs_yield_required entry \<or>
   mtrs_remaining entry > 0 \<or>
   sa_missed_yield (mtrs_scheduler entry)"
  by (simp add: missed_tick_outer_requested_def
      missed_tick_replay_and_mark_yield missed_tick_replay_and_mark_def
      missed_tick_mark_replay_yield_def)

end
