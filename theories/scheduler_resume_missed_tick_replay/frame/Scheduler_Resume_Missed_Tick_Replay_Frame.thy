theory Scheduler_Resume_Missed_Tick_Replay_Frame
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Core.Scheduler_Resume_Missed_Tick_Replay_Core"
begin

text \<open>
  These frame lemmas isolate fields that the unlocked tick never changes.
  They keep later replay inductions independent of the size of any due prefix.
\<close>

lemma add_ready_frames_tick [simp]:
  "sa_tick (add_ready_node n s) = sa_tick s"
  by (cases n) (simp_all add: Let_def)

lemma add_ready_frames_missed_ticks [simp]:
  "sa_missed_ticks (add_ready_node n s) = sa_missed_ticks s"
  by (cases n) (simp_all add: Let_def)

lemma add_ready_frames_delayed_role [simp]:
  "sa_current_role_a (add_ready_node n s) = sa_current_role_a s"
  by (cases n) (simp_all add: Let_def)

lemma add_ready_frames_overflows [simp]:
  "sa_overflows (add_ready_node n s) = sa_overflows s"
  by (cases n) (simp_all add: Let_def)

lemma add_ready_frames_missed_yield [simp]:
  "sa_missed_yield (add_ready_node n s) = sa_missed_yield s"
  by (cases n) (simp_all add: Let_def)

lemma add_ready_frames_yield_count [simp]:
  "sa_yield_count (add_ready_node n s) = sa_yield_count s"
  by (cases n) (simp_all add: Let_def)

lemma fold_add_ready_frames_tick [simp]:
  "sa_tick (fold add_ready_node ns s) = sa_tick s"
  by (induction ns arbitrary: s) simp_all

lemma fold_add_ready_frames_missed_ticks [simp]:
  "sa_missed_ticks (fold add_ready_node ns s) = sa_missed_ticks s"
  by (induction ns arbitrary: s) simp_all

lemma fold_add_ready_frames_delayed_role [simp]:
  "sa_current_role_a (fold add_ready_node ns s) = sa_current_role_a s"
  by (induction ns arbitrary: s) simp_all

lemma fold_add_ready_frames_overflows [simp]:
  "sa_overflows (fold add_ready_node ns s) = sa_overflows s"
  by (induction ns arbitrary: s) simp_all

lemma fold_add_ready_frames_missed_yield [simp]:
  "sa_missed_yield (fold add_ready_node ns s) = sa_missed_yield s"
  by (induction ns arbitrary: s) simp_all

lemma fold_add_ready_frames_yield_count [simp]:
  "sa_yield_count (fold add_ready_node ns s) = sa_yield_count s"
  by (induction ns arbitrary: s) simp_all

lemma tick_unlocked_frames_missed_ticks [simp]:
  "sa_missed_ticks (tick_unlocked_abs s) = sa_missed_ticks s"
  by (simp add: tick_unlocked_abs_def swap_delayed_roles_def
      put_current_delayed_def Let_def)

lemma tick_unlocked_frames_missed_yield [simp]:
  "sa_missed_yield (tick_unlocked_abs s) = sa_missed_yield s"
  by (simp add: tick_unlocked_abs_def swap_delayed_roles_def
      put_current_delayed_def Let_def)

lemma tick_unlocked_frames_yield_count [simp]:
  "sa_yield_count (tick_unlocked_abs s) = sa_yield_count s"
  by (simp add: tick_unlocked_abs_def swap_delayed_roles_def
      put_current_delayed_def Let_def)

lemma tick_unlocked_tick [simp]:
  "sa_tick (tick_unlocked_abs s) = sa_tick s + 1"
  by (simp add: tick_unlocked_abs_def swap_delayed_roles_def
      put_current_delayed_def Let_def)

lemma tick_unlocked_wrap_role:
  assumes wrap: "sa_tick s + 1 = 0"
  shows
    "sa_current_role_a (tick_unlocked_abs s) =
       (\<not> sa_current_role_a s) \<and>
     sa_overflows (tick_unlocked_abs s) = Suc (sa_overflows s)"
  using wrap
  by (simp add: tick_unlocked_abs_def swap_delayed_roles_def
      put_current_delayed_def Let_def)

lemma tick_unlocked_no_wrap_role:
  assumes no_wrap: "sa_tick s + 1 \<noteq> 0"
  shows
    "sa_current_role_a (tick_unlocked_abs s) =
       sa_current_role_a s \<and>
     sa_overflows (tick_unlocked_abs s) = sa_overflows s"
  using no_wrap
  by (simp add: tick_unlocked_abs_def swap_delayed_roles_def
      put_current_delayed_def Let_def)

text \<open>
  Every replay iteration imports the already-proved arbitrary due-prefix fold.
  Thus a single missed tick may wake any finite due prefix; this model does not
  assume zero or one awakened task.
\<close>

theorem missed_tick_body_is_due_prefix_fold:
  "mtrs_scheduler (missed_tick_body_step r) =
   (due_prefix_fold_state
      (due_tick_entry_abs (mtrs_scheduler r))
      (due_tick_sequence_abs (mtrs_scheduler r)))
       \<lparr>sa_missed_ticks := mtrs_remaining r - 1\<rparr>"
  by (simp add: tick_unlocked_abs_is_due_prefix_fold)

theorem missed_tick_body_wrap_role:
  assumes wrap:
    "sa_tick (mtrs_scheduler r) + 1 = 0"
  shows
    "sa_current_role_a
       (mtrs_scheduler (missed_tick_body_step r)) =
       (\<not> sa_current_role_a (mtrs_scheduler r)) \<and>
     sa_overflows (mtrs_scheduler (missed_tick_body_step r)) =
       Suc (sa_overflows (mtrs_scheduler r))"
  using tick_unlocked_wrap_role[OF wrap] by simp

theorem missed_tick_body_no_wrap_role:
  assumes no_wrap:
    "sa_tick (mtrs_scheduler r) + 1 \<noteq> 0"
  shows
    "sa_current_role_a
       (mtrs_scheduler (missed_tick_body_step r)) =
       sa_current_role_a (mtrs_scheduler r) \<and>
     sa_overflows (mtrs_scheduler (missed_tick_body_step r)) =
       sa_overflows (mtrs_scheduler r)"
  using tick_unlocked_no_wrap_role[OF no_wrap] by simp

end
