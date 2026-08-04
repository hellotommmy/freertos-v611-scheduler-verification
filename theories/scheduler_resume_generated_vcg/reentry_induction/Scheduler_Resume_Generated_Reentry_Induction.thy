theory Scheduler_Resume_Generated_Reentry_Induction
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Gate.Scheduler_Resume_Generated_Reentry_Gate"
begin

text \<open>
  The generated pending-ready drain loop, executed to completion over an
  arbitrary finite pending list.  The proof is a plain list induction: each
  step consumes the head through the end-to-end body theorem at the current
  gate state and continues at the drained state, which the re-entry theorem
  shows is a gate state for the tail.  The postcondition returns NULL and
  the folded yield word, and hands the exit state over as a gate state for
  the empty pending list -- exactly what the missed-tick continuation of
  \<open>xTaskResumeAll'\<close> will consume.  No pending length, task identity,
  priority, ring topology or heap layout is fixed anywhere.
\<close>

definition resume_pending_drained_all_abs ::
  "'tid list \<Rightarrow> 'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "resume_pending_drained_all_abs ts a =
     foldl (\<lambda>acc u. resume_one_pending_abs u acc) a ts"

lemma resume_pending_drained_all_abs_simps:
  "resume_pending_drained_all_abs [] a = a"
  "resume_pending_drained_all_abs (u # us) a =
     resume_pending_drained_all_abs us (resume_one_pending_abs u a)"
  by (simp_all add: resume_pending_drained_all_abs_def)

lemma resume_pending_generated_loop_drains_aux:
  fixes ts :: "'tid list"
  shows
    "\<And>c a C S generic_raw event_raw y.
       resume_pending_gate_entry_rel D R c a C S generic_raw
         event_raw \<Longrightarrow>
       rpc_tasks C = ts \<Longrightarrow>
       R = generated_scheduler_roots \<Longrightarrow>
       whileLoop resume_pending_generated_cond
         resume_pending_generated_body
         (resume_pending_next_head_tcb D ts, y) \<bullet> c
       \<lbrace>\<lambda>r s. \<exists>C' S' gr' er' yw.
          r = Result (NULL, yw) \<and>
          resume_pending_gate_entry_rel D R s
            (resume_pending_drained_all_abs ts a) C' S' gr' er' \<and>
          rpc_tasks C' = [] \<and>
          rpc_live C' = rpc_live C \<and>
          rpc_current_priority C' = rpc_current_priority C \<and>
          rpc_priority C' = rpc_priority C \<and>
          ((yw \<noteq> 0) \<longleftrightarrow>
             ((y \<noteq> 0) \<or>
              (\<exists>u\<in>set ts.
                 rpc_current_priority C \<le> rpc_priority C u)))\<rbrace>"
proof (induction ts)
  case Nil
  have head_null:
    "resume_pending_next_head_tcb D ([] :: 'tid list) = NULL"
    by (simp add: resume_pending_next_head_tcb_def)
  have cond_false:
    "\<not> resume_pending_generated_cond
       (resume_pending_next_head_tcb D ([] :: 'tid list), y) c"
    using head_null
    by (simp add: resume_pending_generated_cond_def)
  show ?case
    apply (subst runs_to_whileLoop_cond_fail
        [of resume_pending_generated_cond
            "(resume_pending_next_head_tcb D ([] :: 'tid list), y)" c,
          OF cond_false])
    apply runs_to_vcg
     apply (simp add: resume_pending_next_head_tcb_def)
    using Nil
    by (auto simp: resume_pending_drained_all_abs_simps
        intro: exI[of _ C] exI[of _ S] exI[of _ generic_raw]
               exI[of _ event_raw] exI[of _ y])
next
  case (Cons t rest)
  note rel = Cons.prems(1)
  note tasks = Cons.prems(2)
  note roots = Cons.prems(3)
  have head_eq:
    "resume_pending_next_head_tcb D (t # rest) = sd_tcb_ptr D t"
    by (simp add: resume_pending_next_head_tcb_def)
  have t_live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  have observation:
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a"
    by (rule resume_pending_gate_task_observationD[OF rel])
  have live_abs: "t \<in> sa_live a"
    using rel t_live
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  have guard_t: "c_guard (sd_tcb_ptr D t)"
    using TaskObservationRel_liveD[OF observation live_abs] by blast
  have head_not_null: "sd_tcb_ptr D t \<noteq> NULL"
    by (rule c_guard_NULL[OF guard_t])
  have cond_true:
    "resume_pending_generated_cond (sd_tcb_ptr D t, y) c"
    using head_not_null
    by (simp add: resume_pending_generated_cond_def)
  note body = resume_pending_generated_body_exact[OF rel tasks roots]
  note reentry = resume_pending_gate_reentry[OF rel tasks roots]
  note ctx = resume_pending_drained_context_components[of C t rest]
  show ?case
    apply (simp only: head_eq)
    apply (subst whileLoop_unroll)
    apply (simp only: runs_to_condition_iff)
    apply (simp only: cond_true if_True)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF body])
    apply (clarsimp split del: if_split)
    apply (rule runs_to_weaken[OF Cons.IH[OF reentry _ roots]])
     apply (simp add: ctx)
    apply clarify
    apply (intro exI)
    apply (rule conjI, rule refl)
    apply (rule conjI)
     apply (simp only: resume_pending_drained_all_abs_simps)
    apply (intro conjI)
        apply (simp add: ctx)
       apply (simp add: ctx)
      apply (simp add: ctx)
     apply (simp add: ctx)
    apply (cases "rpc_current_priority C \<le> rpc_priority C t")
     apply (simp add: ctx)
    by (simp add: ctx)
qed

theorem resume_pending_generated_loop_drains:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
  shows
    "whileLoop resume_pending_generated_cond
       resume_pending_generated_body
       (resume_pending_next_head_tcb D (rpc_tasks C), y) \<bullet> c
     \<lbrace>\<lambda>r s. \<exists>C' S' gr' er' yw.
        r = Result (NULL, yw) \<and>
        resume_pending_gate_entry_rel D R s
          (resume_pending_drained_all_abs (rpc_tasks C) a)
          C' S' gr' er' \<and>
        rpc_tasks C' = [] \<and>
        rpc_live C' = rpc_live C \<and>
        rpc_current_priority C' = rpc_current_priority C \<and>
        rpc_priority C' = rpc_priority C \<and>
        ((yw \<noteq> 0) \<longleftrightarrow>
           ((y \<noteq> 0) \<or>
            (\<exists>u\<in>set (rpc_tasks C).
               rpc_current_priority C \<le> rpc_priority C u)))\<rbrace>"
  by (rule resume_pending_generated_loop_drains_aux[OF rel refl roots])

end
