theory Scheduler_V611_Delay_Zero_Refinement
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Increment_Tick_Suspended_Refinement.Scheduler_V611_Increment_Tick_Suspended_Refinement"
begin

text \<open>
  Restricted refinement for exactly vTaskDelay 0.  This source branch does
  not suspend the scheduler, inspect the current TCB, or move a list item.  It
  invokes the named proof-port yield once.  The independently reconstructed
  abstract operation performs request_yield, represented by one increment of
  sa_yield_count.  No theorem in this file covers a positive delay argument.
\<close>

definition scheduler_yield_count_no_wrap :: "globals \<Rightarrow> bool"
where
  "scheduler_yield_count_no_wrap c \<longleftrightarrow>
     eal6_port_yield_count_' c \<noteq> (-1 :: 32 word)"

lemma yield_count_unat_add_one:
  assumes no_wrap: "scheduler_yield_count_no_wrap c"
  shows
    "unat (eal6_port_yield_count_' c + 1) =
       Suc (unat (eal6_port_yield_count_' c))"
  using no_wrap
  unfolding scheduler_yield_count_no_wrap_def
  by (metis add.commute max_word_wrap unatSuc)

text \<open>
  The proof-port counter is a 32-bit observation of an unbounded abstract
  event count.  Relating the word to the low 32 bits of the natural count
  makes wraparound explicit instead of excluding the maximum word.
\<close>

definition yield_count_mod_rel :: "32 word \<Rightarrow> nat \<Rightarrow> bool"
where
  "yield_count_mod_rel w n \<longleftrightarrow> w = of_nat n"

lemma yield_count_mod_rel_request:
  assumes rel: "yield_count_mod_rel w n"
  shows "yield_count_mod_rel (w + 1) (Suc n)"
  using rel by (simp add: yield_count_mod_rel_def)

definition scheduler_control_mod_rel ::
  "globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
where
  "scheduler_control_mod_rel c a \<longleftrightarrow>
     xTickCount_' c = sa_tick a \<and>
     unat (uxSchedulerSuspended_' c) = sa_suspend_depth a \<and>
     unat (uxMissedTicks_' c) = sa_missed_ticks a \<and>
     xMissedYield_' c = (if sa_missed_yield a then 1 else 0) \<and>
     yield_count_mod_rel (eal6_port_yield_count_' c) (sa_yield_count a)"

lemma scheduler_control_mod_rel_request_yield:
  assumes rel: "scheduler_control_mod_rel c a"
  shows
    "scheduler_control_mod_rel
       (eal6_port_yield_count_'_update (\<lambda>n. n + 1) c)
       (request_yield a)"
  using rel yield_count_mod_rel_request
  by (simp add: scheduler_control_mod_rel_def request_yield_def)

theorem eal6_port_yield_mod_refines_request_yield:
  assumes rel: "scheduler_control_mod_rel c a"
  shows
    "eal6_port_yield' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = eal6_port_yield_count_'_update (\<lambda>n. n + 1) c \<and>
       scheduler_control_mod_rel t (request_yield a)
     \<rbrace>"
proof -
  have preserved:
    "scheduler_control_mod_rel
       (eal6_port_yield_count_'_update (\<lambda>n. n + 1) c)
       (request_yield a)"
    by (rule scheduler_control_mod_rel_request_yield[OF rel])
  show ?thesis
    unfolding eal6_port_yield'_def
    apply runs_to_vcg
    using preserved by simp
qed

text \<open>
  A non-vacuity witness aligns all scheduler-control fields and starts the
  proof-port yield ledger at zero.  The zero-delay source path requires no
  heap or current-task validity premise.
\<close>

lemma scheduler_delay_zero_pre_witness:
  "scheduler_control_rel
     (c\<lparr>
        xMissedYield_' := 0,
        eal6_port_yield_count_' := 0
      \<rparr>)
     (a\<lparr>
        sa_tick := xTickCount_' c,
        sa_missed_ticks := unat (uxMissedTicks_' c),
        sa_suspend_depth := unat (uxSchedulerSuspended_' c),
        sa_missed_yield := False,
        sa_yield_count := 0
      \<rparr>) \<and>
   scheduler_yield_count_no_wrap
     (c\<lparr>
        xMissedYield_' := 0,
        eal6_port_yield_count_' := 0
      \<rparr>)"
  by (simp add: scheduler_control_rel_def
      scheduler_yield_count_no_wrap_def)

lemma scheduler_control_rel_request_yield:
  assumes rel: "scheduler_control_rel c a"
      and no_wrap: "scheduler_yield_count_no_wrap c"
  shows
    "scheduler_control_rel
       (eal6_port_yield_count_'_update (\<lambda>n. n + 1) c)
       (a\<lparr>sa_yield_count := Suc (sa_yield_count a)\<rparr>)"
proof -
  have step:
    "unat (eal6_port_yield_count_' c + 1) =
       Suc (unat (eal6_port_yield_count_' c))"
    using yield_count_unat_add_one[OF no_wrap] .
  show ?thesis
    using rel step
    by (simp add: scheduler_control_rel_def)
qed

text \<open>
  Exact source semantics remain modulo 2^32 and therefore need no no-wrap
  premise.  The bound is needed only by the word-to-natural abstraction step.
\<close>

theorem vTaskDelay_zero_result:
  "vTaskDelay' 0 \<bullet> c
   \<lbrace>\<lambda>r t.
     r = Result () \<and>
     t = eal6_port_yield_count_'_update (\<lambda>n. n + 1) c
   \<rbrace>"
proof -
  show ?thesis
    unfolding vTaskDelay'_def eal6_port_yield'_def
    apply runs_to_vcg
    done
qed

definition scheduler_delay_zero_frame ::
  "globals \<Rightarrow> globals \<Rightarrow> bool"
where
  "scheduler_delay_zero_frame c t \<longleftrightarrow>
     t_hrs_' t = t_hrs_' c \<and>
     pxCurrentTCB_' t = pxCurrentTCB_' c \<and>
     pxDelayedTaskList_' t = pxDelayedTaskList_' c \<and>
     pxOverflowDelayedTaskList_' t = pxOverflowDelayedTaskList_' c \<and>
     uxTopReadyPriority_' t = uxTopReadyPriority_' c \<and>
     uxCurrentNumberOfTasks_' t = uxCurrentNumberOfTasks_' c \<and>
     xTickCount_' t = xTickCount_' c \<and>
     uxSchedulerSuspended_' t = uxSchedulerSuspended_' c \<and>
     uxMissedTicks_' t = uxMissedTicks_' c \<and>
     xMissedYield_' t = xMissedYield_' c \<and>
     xNumOfOverflows_' t = xNumOfOverflows_' c \<and>
     eal6_port_critical_depth_' t = eal6_port_critical_depth_' c \<and>
     eal6_port_interrupts_disabled_' t =
       eal6_port_interrupts_disabled_' c"

corollary vTaskDelay_zero_strong_frame:
  assumes no_wrap: "scheduler_yield_count_no_wrap c"
  shows
    "vTaskDelay' 0 \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       eal6_port_yield_count_' t = eal6_port_yield_count_' c + 1 \<and>
       unat (eal6_port_yield_count_' t) =
         Suc (unat (eal6_port_yield_count_' c)) \<and>
       scheduler_delay_zero_frame c t
     \<rbrace>"
proof -
  have step:
    "unat (eal6_port_yield_count_' c + 1) =
       Suc (unat (eal6_port_yield_count_' c))"
    using yield_count_unat_add_one[OF no_wrap] .
  note exact = vTaskDelay_zero_result[where c=c]
  show ?thesis
    apply (rule runs_to_weaken[OF exact])
    using step
    apply (clarsimp simp: scheduler_delay_zero_frame_def)
    done
qed

theorem vTaskDelay_zero_refines:
  assumes rel: "scheduler_control_rel c a"
      and no_wrap: "scheduler_yield_count_no_wrap c"
  shows
    "vTaskDelay' 0 \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = eal6_port_yield_count_'_update (\<lambda>n. n + 1) c \<and>
       scheduler_control_rel t (task_delay_abs 0 a)
     \<rbrace>"
proof -
  have abstract_step:
    "task_delay_abs 0 a =
       a\<lparr>sa_yield_count := Suc (sa_yield_count a)\<rparr>"
    using task_delay_zero[of a]
    by (simp add: request_yield_def)
  have yielded:
    "scheduler_control_rel
       (eal6_port_yield_count_'_update (\<lambda>n. n + 1) c)
       (a\<lparr>sa_yield_count := Suc (sa_yield_count a)\<rparr>)"
    using scheduler_control_rel_request_yield[OF rel no_wrap] .
  note exact = vTaskDelay_zero_result[where c=c]
  show ?thesis
    apply (rule runs_to_weaken[OF exact])
    using yielded abstract_step
    apply clarsimp
    done
qed

text \<open>
  The positive-delay branch remains open.  It requires a current-TCB
  representation, general-N ready-list removal, ordered delayed-list insertion,
  and a refinement of the suspend/resume protocol; none is inferred here.
\<close>

end
