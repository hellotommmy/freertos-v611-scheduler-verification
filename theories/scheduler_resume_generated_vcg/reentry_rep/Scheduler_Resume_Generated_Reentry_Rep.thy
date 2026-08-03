theory Scheduler_Resume_Generated_Reentry_Rep
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Lists.Scheduler_Resume_Generated_Reentry_Lists"
begin

text \<open>
  The representation, scalar, role and current clauses of re-entry.  The
  eight scheduler roots at the drained heap represent the abstract one-task
  resume through the drained raw families and the snapshot matches; the
  scalar words transfer because the body writes only the heap and the
  top-priority word, whose raise is mirrored exactly by the abstract
  \<open>max\<close>.
\<close>

context
  fixes D :: "'tid scheduler_decode"
    and R :: scheduler_roots
    and c :: "Scheduler_V611_Parse.globals"
    and a :: "'tid scheduler_abs"
    and C :: "('tid, xLIST_C ptr) resume_pending_context"
    and S :: "('tid, xLIST_C ptr) resume_pending_snapshot"
    and generic_raw event_raw ::
      "xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs"
    and t :: 'tid and rest :: "'tid list"
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and roots: "R = generated_scheduler_roots"
begin

lemma reentry_drained_heap_eqL:
  "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
     (resume_pending_ready_inserted_state D C t generic_raw c)) =
   hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
     (resume_pending_ready_inserted_state D C t generic_raw c))"
  by simp

lemma reentry_generic_root_rawL:
  assumes root_in: "g \<in> rpc_generic_roots C"
  shows
    "raw_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
       g (resume_pending_drained_generic_fam C D t c generic_raw g)"
proof -
  have pre:
    "scheduler_family_pre_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
       (rpc_generic_roots C)
       (resume_pending_drained_generic_fam C D t c generic_raw)
       (rpc_live C) D"
    using resume_pending_drained_generic_family[OF rel tasks] by blast
  show ?thesis
    using pre root_in
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
qed

lemma reentry_generic_root_schedL:
  assumes root_in: "g \<in> rpc_generic_roots C"
  shows
    "sched_xlist_rel (sd_node_decode D)
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
       g (rps_generic_family (resume_pending_drained_snapshot C t S) g)"
proof -
  have relabel:
    "xlist_relabel (sd_node_decode D)
       (resume_pending_drained_generic_fam C D t c generic_raw g)
       (rps_generic_family (resume_pending_drained_snapshot C t S) g)"
    using resume_pending_drained_generic_relabel[OF rel tasks root_in]
    by (simp add: resume_pending_drained_snapshot_def)
  show ?thesis
    using reentry_generic_root_rawL[OF root_in] relabel
    by (auto simp: sched_xlist_rel_def)
qed

lemma reentry_pending_schedL:
  "sched_xlist_rel (sd_node_decode D)
     (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
       (resume_pending_ready_inserted_state D C t generic_raw c)))
     (rpc_pending_root C)
     (rps_event_family (resume_pending_drained_snapshot C t S)
       (rpc_pending_root C))"
proof -
  have pending_root: "rpc_pending_root C \<in> rpc_event_roots C"
    using resume_pending_gate_pure_entryD[OF rel]
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_context_wf_def)
  note family = resume_pending_ready_insert_event_family_frame[
    OF rel tasks]
  have sched:
    "sched_xlist_rel (sd_node_decode D)
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
       (rpc_pending_root C)
       (rps_event_family (resume_pending_event_unlink_state C t S)
         (rpc_pending_root C))"
    by (rule scheduler_event_root_family_sched_xlistD[
      OF family pending_root])
  have snapshot_eq:
    "rps_event_family (resume_pending_drained_snapshot C t S)
       (rpc_pending_root C) =
     rps_event_family (resume_pending_event_unlink_state C t S)
       (rpc_pending_root C)"
    by (simp add: resume_pending_drained_event_at
        resume_pending_event_unlink_state_def)
  show ?thesis using sched snapshot_eq by simp
qed

theorem resume_pending_drained_lists_rel:
  "scheduler_lists_rel D R
     (resume_pending_ready_inserted_state D C t generic_raw c)
     (resume_one_pending_abs t a)"
proof -
  have ready_roots_in:
    "\<And>p. p < 4 \<Longrightarrow>
       abi_list_ptr (sr_ready R p) \<in> rpc_generic_roots C"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  have da_in: "abi_list_ptr (sr_delayed_a R) \<in> rpc_generic_roots C"
    and db_in: "abi_list_ptr (sr_delayed_b R) \<in> rpc_generic_roots C"
    and susp_in: "abi_list_ptr (sr_suspended R) \<in> rpc_generic_roots C"
    using resume_pending_gate_role_rootsD[OF rel] by blast+
  have pending_eq:
    "rpc_pending_root C = abi_list_ptr (sr_pending R)"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  show ?thesis
    unfolding scheduler_lists_rel_def Let_def
  proof (intro conjI allI impI)
    fix p :: nat
    assume p_bound: "p < 4"
    show
      "sched_xlist_rel (sd_node_decode D)
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
           (resume_pending_ready_inserted_state D C t generic_raw c)))
         (abi_list_ptr (sr_ready R p))
         (sa_ready (resume_one_pending_abs t a) p)"
      using reentry_generic_root_schedL[OF ready_roots_in[OF p_bound]]
        reentry_sa_ready_matchL[OF rel tasks roots p_bound]
      by simp
  next
    show
      "sched_xlist_rel (sd_node_decode D)
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
           (resume_pending_ready_inserted_state D C t generic_raw c)))
         (abi_list_ptr (sr_delayed_a R))
         (sa_delayed_a (resume_one_pending_abs t a))"
      using reentry_generic_root_schedL[OF da_in]
        reentry_sa_delayed_a_matchL[OF rel tasks roots]
      by simp
  next
    show
      "sched_xlist_rel (sd_node_decode D)
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
           (resume_pending_ready_inserted_state D C t generic_raw c)))
         (abi_list_ptr (sr_delayed_b R))
         (sa_delayed_b (resume_one_pending_abs t a))"
      using reentry_generic_root_schedL[OF db_in]
        reentry_sa_delayed_b_matchL[OF rel tasks roots]
      by simp
  next
    show
      "sched_xlist_rel (sd_node_decode D)
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
           (resume_pending_ready_inserted_state D C t generic_raw c)))
         (abi_list_ptr (sr_pending R))
         (sa_pending (resume_one_pending_abs t a))"
      using reentry_pending_schedL pending_eq
        reentry_sa_pending_matchL[OF rel tasks roots]
      by simp
  next
    show
      "sched_xlist_rel (sd_node_decode D)
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
           (resume_pending_ready_inserted_state D C t generic_raw c)))
         (abi_list_ptr (sr_suspended R))
         (sa_suspended (resume_one_pending_abs t a))"
      using reentry_generic_root_schedL[OF susp_in]
        reentry_sa_suspended_matchL[OF rel tasks roots]
      by simp
  qed
qed

theorem resume_pending_drained_scalar_rel:
  "scheduler_scalar_rel
     (resume_pending_ready_inserted_state D C t generic_raw c)
     (resume_one_pending_abs t a)"
proof -
  have entry_scalar: "scheduler_scalar_rel c a"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  have abs_eqs:
    "sa_tick (resume_one_pending_abs t a) = sa_tick a \<and>
     sa_suspend_depth (resume_one_pending_abs t a) =
       sa_suspend_depth a \<and>
     sa_missed_ticks (resume_one_pending_abs t a) =
       sa_missed_ticks a \<and>
     sa_missed_yield (resume_one_pending_abs t a) =
       sa_missed_yield a \<and>
     sa_overflows (resume_one_pending_abs t a) = sa_overflows a \<and>
     sa_live (resume_one_pending_abs t a) = sa_live a \<and>
     sa_yield_count (resume_one_pending_abs t a) = sa_yield_count a \<and>
     sa_top_ready (resume_one_pending_abs t a) =
       max (sa_top_ready a) (sa_priority a t)"
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def
        resume_add_ready_with_key_abs_def Let_def)
  have entry_top_eq:
    "rpc_entry_top C =
       unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_' c)"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  have top_word:
    "unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_'
       (resume_pending_ready_inserted_state D C t generic_raw c)) =
     max (rpc_entry_top C) (rpc_priority C t)"
    using resume_pending_top_raised_semantics[OF rel tasks]
      resume_pending_ready_inserted_top[of D C t generic_raw c]
    by simp
  have entry_top_abs:
    "unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_' c) =
       sa_top_ready a"
    using entry_scalar by (simp add: scheduler_scalar_rel_def)
  have top_match:
    "unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_'
       (resume_pending_ready_inserted_state D C t generic_raw c)) =
     sa_top_ready (resume_one_pending_abs t a)"
    using top_word entry_top_eq entry_top_abs abs_eqs
      reentry_priority_eqL[OF rel tasks roots]
    by simp
  show ?thesis
    unfolding scheduler_scalar_rel_def
    by (simp add: resume_pending_ready_inserted_globals abs_eqs
        top_match entry_scalar[unfolded scheduler_scalar_rel_def])
qed

theorem resume_pending_drained_role_rel:
  "scheduler_role_rel R
     (resume_pending_ready_inserted_state D C t generic_raw c)
     (resume_one_pending_abs t a)"
proof -
  have entry_role: "scheduler_role_rel R c a"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  have flag_eq:
    "sa_current_role_a (resume_one_pending_abs t a) =
       sa_current_role_a a"
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def
        resume_add_ready_with_key_abs_def Let_def)
  show ?thesis
    unfolding scheduler_role_rel_def
    by (simp add: resume_pending_ready_inserted_globals flag_eq
        entry_role[unfolded scheduler_role_rel_def])
qed

theorem resume_pending_drained_current_rel:
  "scheduler_current_rel D
     (resume_pending_ready_inserted_state D C t generic_raw c)
     (resume_one_pending_abs t a)"
proof -
  have entry_current: "scheduler_current_rel D c a"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  have current_eq:
    "sa_current (resume_one_pending_abs t a) = sa_current a"
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def
        resume_add_ready_with_key_abs_def Let_def)
  show ?thesis
  proof (cases "sa_current a")
    case None
    then show ?thesis
      using entry_current
      by (simp add: scheduler_current_rel_def current_eq
          resume_pending_ready_inserted_pxCurrentTCB)
  next
    case (Some cur)
    then show ?thesis
      using entry_current
      by (simp add: scheduler_current_rel_def current_eq
          resume_pending_ready_inserted_pxCurrentTCB)
  qed
qed

end

end
