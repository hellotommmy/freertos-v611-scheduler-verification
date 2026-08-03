theory Scheduler_Resume_Generated_Reentry_Lists
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Abs_Bridge.Scheduler_Resume_Generated_Reentry_Abs_Bridge"
begin

text \<open>
  The representation clauses of re-entry.  Every scheduler root's ring at
  the drained heap represents the corresponding list of the abstract
  one-task resume: the ready queue at the awakened priority gains the task
  with its captured key, its blocked list loses it, the pending list loses
  its Event item, and the other five roots are untouched on both sides.
  The scalar, role and current clauses transfer because the drain writes
  the heap and the top-priority word only.
\<close>

section \<open>Globals untouched by the drain body\<close>

lemma resume_pending_ready_inserted_globals:
  "Scheduler_V611_Parse.globals.pxDelayedTaskList_'
     (resume_pending_ready_inserted_state D C t generic_raw c) =
   Scheduler_V611_Parse.globals.pxDelayedTaskList_' c \<and>
   Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_'
     (resume_pending_ready_inserted_state D C t generic_raw c) =
   Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_' c \<and>
   Scheduler_V611_Parse.globals.xTickCount_'
     (resume_pending_ready_inserted_state D C t generic_raw c) =
   Scheduler_V611_Parse.globals.xTickCount_' c \<and>
   Scheduler_V611_Parse.globals.uxSchedulerSuspended_'
     (resume_pending_ready_inserted_state D C t generic_raw c) =
   Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c \<and>
   Scheduler_V611_Parse.globals.uxMissedTicks_'
     (resume_pending_ready_inserted_state D C t generic_raw c) =
   Scheduler_V611_Parse.globals.uxMissedTicks_' c \<and>
   Scheduler_V611_Parse.globals.xMissedYield_'
     (resume_pending_ready_inserted_state D C t generic_raw c) =
   Scheduler_V611_Parse.globals.xMissedYield_' c \<and>
   Scheduler_V611_Parse.globals.xNumOfOverflows_'
     (resume_pending_ready_inserted_state D C t generic_raw c) =
   Scheduler_V611_Parse.globals.xNumOfOverflows_' c \<and>
   Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_'
     (resume_pending_ready_inserted_state D C t generic_raw c) =
   Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c \<and>
   Scheduler_V611_Parse.globals.eal6_port_yield_count_'
     (resume_pending_ready_inserted_state D C t generic_raw c) =
   Scheduler_V611_Parse.globals.eal6_port_yield_count_' c \<and>
   Scheduler_V611_Parse.globals.xSchedulerRunning_'
     (resume_pending_ready_inserted_state D C t generic_raw c) =
   Scheduler_V611_Parse.globals.xSchedulerRunning_' c \<and>
   Scheduler_V611_Parse.globals.eal6_port_critical_depth_'
     (resume_pending_ready_inserted_state D C t generic_raw c) =
   Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c \<and>
   Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_'
     (resume_pending_ready_inserted_state D C t generic_raw c) =
   Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' c"
  by (simp add: resume_pending_ready_inserted_state_def
      resume_pending_top_raised_state_def scheduler_mem_state_def
      Let_def)

section \<open>Physical distinctness of the generated roots\<close>

lemma generated_nat_lt_4_cases:
  fixes p :: nat
  assumes "p < 4"
  obtains "p = 0" | "p = 1" | "p = 2" | "p = 3"
  using assms by (auto simp: eval_nat_numeral less_Suc_eq)

lemma generated_ready_root_neq_roles:
  assumes p_bound: "p < 4"
  shows
    "sr_ready generated_scheduler_roots p \<noteq>
       sr_delayed_a generated_scheduler_roots \<and>
     sr_ready generated_scheduler_roots p \<noteq>
       sr_delayed_b generated_scheduler_roots \<and>
     sr_ready generated_scheduler_roots p \<noteq>
       sr_suspended generated_scheduler_roots \<and>
     sr_ready generated_scheduler_roots p \<noteq>
       sr_pending generated_scheduler_roots"
  by (cases rule: generated_nat_lt_4_cases[OF p_bound])
     (simp_all add: generated_scheduler_roots_def
       Scheduler_V611_Parse.pxReadyTasksLists_'_def
       Scheduler_V611_Parse.xDelayedTaskList1_'_def
       Scheduler_V611_Parse.xDelayedTaskList2_'_def
       Scheduler_V611_Parse.xPendingReadyList_'_def
       Scheduler_V611_Parse.xSuspendedTaskList_'_def
       array_ptr_index_def ptr_add_def
       Scheduler_V611_Parse.xLIST_C_size_of)

lemma generated_ready_root_inj:
  assumes p_bound: "p < 4" and q_bound: "q < 4"
    and eq: "sr_ready generated_scheduler_roots p =
             sr_ready generated_scheduler_roots q"
  shows "p = q"
  using eq
  by (cases rule: generated_nat_lt_4_cases[OF p_bound];
      cases rule: generated_nat_lt_4_cases[OF q_bound])
     (simp_all add: generated_scheduler_roots_def
       Scheduler_V611_Parse.pxReadyTasksLists_'_def
       array_ptr_index_def ptr_add_def
       Scheduler_V611_Parse.xLIST_C_size_of)

section \<open>Snapshot families match the abstract one-task resume\<close>

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

lemma reentry_pureL: "resume_pending_entry_rel C S"
  by (rule resume_pending_gate_pure_entryD[OF rel])

lemma reentry_neL:
  "rpc_generic_owner C t \<noteq> rpc_ready_root C (rpc_priority C t)"
  using resume_pending_entry_head_facts[OF reentry_pureL tasks] by blast

lemma reentry_t_liveL: "t \<in> rpc_live C"
  by (rule resume_pending_gate_head_liveD[OF rel tasks])

lemma reentry_pri_boundL: "rpc_priority C t < 4"
  using resume_pending_entry_head_facts[OF reentry_pureL tasks] by blast

lemma reentry_target_eqL:
  "rpc_ready_root C (rpc_priority C t) =
     abi_list_ptr (sr_ready R (rpc_priority C t))"
  using rel reentry_t_liveL
  unfolding resume_pending_gate_entry_rel_def Let_def by blast

lemma reentry_ready_family_eqL:
  assumes p_bound: "p < 4"
  shows
    "rps_generic_family S (abi_list_ptr (sr_ready R p)) = sa_ready a p"
  using rel p_bound
  unfolding resume_pending_gate_entry_rel_def Let_def by blast

lemma reentry_priority_eqL: "rpc_priority C t = sa_priority a t"
  using rel reentry_t_liveL
  unfolding resume_pending_gate_entry_rel_def Let_def by blast

lemma reentry_sa_ready_matchL:
  assumes p_bound: "p < 4"
  shows
    "sa_ready (resume_one_pending_abs t a) p =
       rps_generic_family (resume_pending_drained_snapshot C t S)
         (abi_list_ptr (sr_ready R p))"
proof -
  have abs_side:
    "sa_ready (resume_one_pending_abs t a) p =
       (if p = sa_priority a t
        then list_insert_end_abs (Generic t)
               (pending_generic_key_abs t a) (sa_ready a p)
        else sa_ready a p)"
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def
        resume_add_ready_with_key_abs_def Let_def)
  have key_eq: "pending_generic_key_abs t a = rpc_K_G C t"
    by (rule resume_pending_gate_captured_keyD[OF rel tasks])
  have root_iff:
    "abi_list_ptr (sr_ready R p) =
       rpc_ready_root C (rpc_priority C t) \<longleftrightarrow>
     p = rpc_priority C t"
  proof
    assume "abi_list_ptr (sr_ready R p) =
      rpc_ready_root C (rpc_priority C t)"
    then have "sr_ready generated_scheduler_roots p =
      sr_ready generated_scheduler_roots (rpc_priority C t)"
      using reentry_target_eqL roots by simp
    then show "p = rpc_priority C t"
      by (rule generated_ready_root_inj[OF p_bound
          reentry_pri_boundL])
  next
    assume "p = rpc_priority C t"
    then show "abi_list_ptr (sr_ready R p) =
      rpc_ready_root C (rpc_priority C t)"
      using reentry_target_eqL by simp
  qed
  have owner_ne:
    "abi_list_ptr (sr_ready R p) \<noteq> rpc_generic_owner C t"
  proof
    assume owner_eq:
      "abi_list_ptr (sr_ready R p) = rpc_generic_owner C t"
    have t_in: "t \<in> set (rpc_tasks C)"
      using tasks by simp
    have in_roles:
      "rpc_generic_owner C t \<in>
         {abi_list_ptr (sr_delayed_a R), abi_list_ptr (sr_delayed_b R),
          abi_list_ptr (sr_suspended R)}"
      by (rule resume_pending_gate_owner_in_rolesD[OF rel t_in])
    show False
      using owner_eq in_roles generated_ready_root_neq_roles[OF p_bound]
        roots by auto
  qed
  show ?thesis
  proof (cases "p = rpc_priority C t")
    case True
    have snap:
      "rps_generic_family (resume_pending_drained_snapshot C t S)
         (abi_list_ptr (sr_ready R p)) =
       list_insert_end_abs (Generic t) (rpc_K_G C t)
         (rps_generic_family S (abi_list_ptr (sr_ready R p)))"
      using resume_pending_drained_generic_at[OF reentry_neL,
          of S "abi_list_ptr (sr_ready R p)"] root_iff True
      by simp
    show ?thesis
      using abs_side snap key_eq True reentry_priority_eqL
        reentry_ready_family_eqL[OF p_bound]
      by simp
  next
    case False
    have snap:
      "rps_generic_family (resume_pending_drained_snapshot C t S)
         (abi_list_ptr (sr_ready R p)) =
       rps_generic_family S (abi_list_ptr (sr_ready R p))"
      using resume_pending_drained_generic_at[OF reentry_neL,
          of S "abi_list_ptr (sr_ready R p)"] root_iff False owner_ne
      by simp
    have p_ne_abs: "p \<noteq> sa_priority a t"
      using False reentry_priority_eqL by simp
    show ?thesis
      using abs_side snap p_ne_abs
        reentry_ready_family_eqL[OF p_bound]
      by simp
  qed
qed

lemma reentry_role_match_genericL:
  assumes role_root:
      "root \<in> {abi_list_ptr (sr_delayed_a R),
        abi_list_ptr (sr_delayed_b R), abi_list_ptr (sr_suspended R)}"
    and root_in: "root \<in> rpc_generic_roots C"
    and family_eq: "rps_generic_family S root = side"
    and ne_target:
      "root \<noteq> rpc_ready_root C (rpc_priority C t)"
  shows
    "list_remove_abs (Generic t) side =
       rps_generic_family (resume_pending_drained_snapshot C t S) root"
proof (cases "root = rpc_generic_owner C t")
  case True
  show ?thesis
    using resume_pending_drained_generic_at[OF reentry_neL, of S root]
      ne_target True family_eq
    by simp
next
  case False
  have not_member:
    "Generic t \<notin> set (ring (rps_generic_family S root))"
    using resume_pending_entry_uniqueD[OF reentry_pureL tasks root_in]
      False by simp
  have wf: "xlist_wf (rps_generic_family S root)"
    by (rule resume_pending_entry_wf_atD[OF reentry_pureL root_in])
  have identity:
    "list_remove_abs (Generic t) (rps_generic_family S root) =
       rps_generic_family S root"
    by (rule list_remove_abs_nonmember[OF wf not_member])
  show ?thesis
    using resume_pending_drained_generic_at[OF reentry_neL, of S root]
      ne_target False identity family_eq
    by simp
qed

lemma reentry_sa_delayed_a_matchL:
  "sa_delayed_a (resume_one_pending_abs t a) =
     rps_generic_family (resume_pending_drained_snapshot C t S)
       (abi_list_ptr (sr_delayed_a R))"
proof -
  have abs_side:
    "sa_delayed_a (resume_one_pending_abs t a) =
       list_remove_abs (Generic t) (sa_delayed_a a)"
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def
        resume_add_ready_with_key_abs_def Let_def)
  have ne_target:
    "abi_list_ptr (sr_delayed_a R) \<noteq>
       rpc_ready_root C (rpc_priority C t)"
    using reentry_target_eqL roots
      generated_ready_root_neq_roles[OF reentry_pri_boundL]
    by auto
  show ?thesis
    using abs_side
      reentry_role_match_genericL[OF _ _
        resume_pending_gate_role_family_daD[OF rel] ne_target]
      resume_pending_gate_role_rootsD[OF rel]
    by auto
qed

lemma reentry_sa_delayed_b_matchL:
  "sa_delayed_b (resume_one_pending_abs t a) =
     rps_generic_family (resume_pending_drained_snapshot C t S)
       (abi_list_ptr (sr_delayed_b R))"
proof -
  have abs_side:
    "sa_delayed_b (resume_one_pending_abs t a) =
       list_remove_abs (Generic t) (sa_delayed_b a)"
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def
        resume_add_ready_with_key_abs_def Let_def)
  have ne_target:
    "abi_list_ptr (sr_delayed_b R) \<noteq>
       rpc_ready_root C (rpc_priority C t)"
    using reentry_target_eqL roots
      generated_ready_root_neq_roles[OF reentry_pri_boundL]
    by auto
  show ?thesis
    using abs_side
      reentry_role_match_genericL[OF _ _
        resume_pending_gate_role_family_dbD[OF rel] ne_target]
      resume_pending_gate_role_rootsD[OF rel]
    by auto
qed

lemma reentry_sa_suspended_matchL:
  "sa_suspended (resume_one_pending_abs t a) =
     rps_generic_family (resume_pending_drained_snapshot C t S)
       (abi_list_ptr (sr_suspended R))"
proof -
  have abs_side:
    "sa_suspended (resume_one_pending_abs t a) =
       list_remove_abs (Generic t) (sa_suspended a)"
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def
        resume_add_ready_with_key_abs_def Let_def)
  have ne_target:
    "abi_list_ptr (sr_suspended R) \<noteq>
       rpc_ready_root C (rpc_priority C t)"
    using reentry_target_eqL roots
      generated_ready_root_neq_roles[OF reentry_pri_boundL]
    by auto
  show ?thesis
    using abs_side
      reentry_role_match_genericL[OF _ _
        resume_pending_gate_role_family_suspD[OF rel] ne_target]
      resume_pending_gate_role_rootsD[OF rel]
    by auto
qed

lemma reentry_sa_pending_matchL:
  "sa_pending (resume_one_pending_abs t a) =
     rps_event_family (resume_pending_drained_snapshot C t S)
       (rpc_pending_root C)"
proof -
  have abs_side:
    "sa_pending (resume_one_pending_abs t a) =
       list_remove_abs (Event t) (sa_pending a)"
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def
        resume_add_ready_with_key_abs_def Let_def)
  have family_eq:
    "rps_event_family S (rpc_pending_root C) = sa_pending a"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  show ?thesis
    using abs_side family_eq
      resume_pending_drained_event_at[of C t S "rpc_pending_root C"]
    by simp
qed

end

end
