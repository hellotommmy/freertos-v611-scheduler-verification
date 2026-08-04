theory Scheduler_Resume_Generated_Drain_Abs_Fold
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Induction.Scheduler_Resume_Generated_Reentry_Induction"
begin

text \<open>
  Connection of the generated drain-loop summary to the outer abstract
  scaffold.  Under the gate relation the pending ring of the abstract state
  is exactly \<open>map Event (rpc_tasks C)\<close>, so the concrete fold
  \<open>resume_pending_drained_all_abs\<close> coincides with the scaffold's
  \<open>drain_pending_abs\<close>, and the loop's yield word is exactly
  \<open>resume_pending_requires_yield\<close>.  The final theorem restates the
  arbitrary-N loop summary in the vocabulary consumed by
  \<open>ResumeOuterDecomp\<close>: the exit abstract state is
  \<open>drain_pending_abs a\<close> and the returned word carries
  \<open>resume_pending_requires_yield a\<close>.
\<close>

lemma drain_pending_nodes_abs_map_Event:
  "drain_pending_nodes_abs (map Event ts) a =
     resume_pending_drained_all_abs ts a"
  by (induction ts arbitrary: a)
     (simp_all add: resume_pending_drained_all_abs_simps)

lemma resume_pending_gate_pending_family_absD:
  assumes rel:
    "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows "rps_event_family S (rpc_pending_root C) = sa_pending a"
  using rel
  unfolding resume_pending_gate_entry_rel_def Let_def
  by blast

lemma resume_pending_gate_live_absD:
  assumes rel:
    "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows "rpc_live C = sa_live a"
  using rel
  unfolding resume_pending_gate_entry_rel_def Let_def
  by blast

lemma resume_pending_gate_priority_absD:
  assumes rel:
    "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows "\<forall>t\<in>rpc_live C. rpc_priority C t = sa_priority a t"
  using rel
  unfolding resume_pending_gate_entry_rel_def Let_def
  by blast

lemma resume_pending_gate_current_absD:
  assumes rel:
    "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows "\<exists>current\<in>rpc_live C.
     sa_current a = Some current \<and>
     rpc_current_priority C = rpc_priority C current"
  using rel
  unfolding resume_pending_gate_entry_rel_def Let_def
  by blast

lemma resume_pending_gate_tasks_ringD:
  assumes rel:
    "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows "ring (rps_event_family S (rpc_pending_root C)) =
     map Event (rpc_tasks C)"
proof -
  have pure: "resume_pending_entry_rel C S"
    by (rule resume_pending_gate_pure_entryD[OF rel])
  show ?thesis
    using pure
    unfolding resume_pending_entry_rel_def
    by blast
qed

lemma resume_pending_gate_tasks_wfD:
  assumes rel:
    "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows "distinct (rpc_tasks C) \<and> set (rpc_tasks C) \<subseteq> rpc_live C"
proof -
  have pure: "resume_pending_entry_rel C S"
    by (rule resume_pending_gate_pure_entryD[OF rel])
  have wf: "resume_pending_context_wf C"
    using pure
    unfolding resume_pending_entry_rel_def
    by blast
  show ?thesis
    using wf
    unfolding resume_pending_context_wf_def
    by blast
qed

lemma resume_pending_gate_pending_ring_absD:
  assumes rel:
    "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows "ring (sa_pending a) = map Event (rpc_tasks C)"
  using resume_pending_gate_tasks_ringD[OF rel]
    resume_pending_gate_pending_family_absD[OF rel]
  by simp

lemma resume_pending_gate_drain_pending_absD:
  assumes rel:
    "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows "drain_pending_abs a =
     resume_pending_drained_all_abs (rpc_tasks C) a"
  by (simp add: drain_pending_abs_def
      resume_pending_gate_pending_ring_absD[OF rel]
      drain_pending_nodes_abs_map_Event)

lemma resume_pending_gate_requires_yieldD:
  assumes rel:
    "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows "resume_pending_requires_yield a \<longleftrightarrow>
     (\<exists>u\<in>set (rpc_tasks C).
        rpc_current_priority C \<le> rpc_priority C u)"
proof -
  obtain current where cur_live: "current \<in> rpc_live C"
    and cur_abs: "sa_current a = Some current"
    and cur_pri: "rpc_current_priority C = rpc_priority C current"
    using resume_pending_gate_current_absD[OF rel] by blast
  have ring_eq: "ring (sa_pending a) = map Event (rpc_tasks C)"
    by (rule resume_pending_gate_pending_ring_absD[OF rel])
  have live_eq: "rpc_live C = sa_live a"
    by (rule resume_pending_gate_live_absD[OF rel])
  have pri_eq: "\<forall>t\<in>rpc_live C. rpc_priority C t = sa_priority a t"
    by (rule resume_pending_gate_priority_absD[OF rel])
  have tasks_live: "set (rpc_tasks C) \<subseteq> rpc_live C"
    using resume_pending_gate_tasks_wfD[OF rel] by blast
  have cur_pri_abs: "rpc_current_priority C = sa_priority a current"
    using cur_pri pri_eq cur_live by simp
  show ?thesis
  proof
    assume "resume_pending_requires_yield a"
    then obtain t where t_ring: "Event t \<in> set (ring (sa_pending a))"
      and t_ge: "sa_priority a current \<le> sa_priority a t"
      unfolding resume_pending_requires_yield_def
      using cur_abs by (auto split: option.splits)
    have t_tasks: "t \<in> set (rpc_tasks C)"
      using t_ring ring_eq by auto
    have t_pri: "rpc_priority C t = sa_priority a t"
      using pri_eq tasks_live t_tasks by blast
    show "\<exists>u\<in>set (rpc_tasks C).
        rpc_current_priority C \<le> rpc_priority C u"
      using t_ge cur_pri_abs t_pri
      by (auto intro!: bexI[OF _ t_tasks])
  next
    assume "\<exists>u\<in>set (rpc_tasks C).
        rpc_current_priority C \<le> rpc_priority C u"
    then obtain u where u_tasks: "u \<in> set (rpc_tasks C)"
      and u_ge: "rpc_current_priority C \<le> rpc_priority C u"
      by blast
    have u_ring: "Event u \<in> set (ring (sa_pending a))"
      using u_tasks ring_eq by simp
    have u_pri: "rpc_priority C u = sa_priority a u"
      using pri_eq tasks_live u_tasks by blast
    show "resume_pending_requires_yield a"
      unfolding resume_pending_requires_yield_def
      using u_ring u_ge cur_pri_abs u_pri cur_abs
      by (auto intro!: exI[of _ u])
  qed
qed

theorem resume_pending_generated_loop_drain_pending_abs:
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
          (drain_pending_abs a) C' S' gr' er' \<and>
        rpc_tasks C' = [] \<and>
        rpc_live C' = rpc_live C \<and>
        rpc_current_priority C' = rpc_current_priority C \<and>
        rpc_priority C' = rpc_priority C \<and>
        ((yw \<noteq> 0) \<longleftrightarrow>
           ((y \<noteq> 0) \<or> resume_pending_requires_yield a))\<rbrace>"
  apply (rule runs_to_weaken
      [OF resume_pending_generated_loop_drains[OF rel roots]])
  by (clarsimp simp:
      resume_pending_gate_drain_pending_absD[OF rel]
      resume_pending_gate_requires_yieldD[OF rel])

end
