theory Scheduler_Resume_Generated_Reentry_Abs_Bridge
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Container_Frame.Scheduler_Resume_Generated_Container_Frame"
begin

text \<open>
  The abstract witness for re-entry is the one-task resume of the entry
  abstract state.  This theory instantiates the invariant-preservation
  theorem at the gate, identifies the abstractly captured wake key with the
  context key, and transports the drained task observation to the new
  abstract state -- which is sound because the abstract resume moves list
  nodes but no task identity or priority.
\<close>

section \<open>The head task is abstractly pending\<close>

lemma resume_pending_gate_head_pending_absD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows "Event t \<in> set (ring (sa_pending a))"
proof -
  have family_eq:
    "rps_event_family S (rpc_pending_root C) = sa_pending a"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  have entry_ring:
    "ring (rps_event_family S (rpc_pending_root C)) =
       Event t # map Event rest"
    using resume_pending_gate_pure_entryD[OF rel] tasks
    by (simp add: resume_pending_entry_rel_def)
  show ?thesis using family_eq entry_ring by simp
qed

lemma resume_pending_gate_core_wfD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows "core_wf a"
  using rel
  unfolding resume_pending_gate_entry_rel_def Let_def by blast

theorem resume_pending_gate_drained_core_wfD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows "core_wf (resume_one_pending_abs t a)"
  by (rule core_wf_resume_one_pending_abs[
    OF resume_pending_gate_core_wfD[OF rel]
      resume_pending_gate_head_pending_absD[OF rel tasks]])

section \<open>The abstractly captured key is the context key\<close>

lemma resume_pending_gate_role_family_daD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows
    "rps_generic_family S (abi_list_ptr (sr_delayed_a R)) =
       sa_delayed_a a"
  using rel
  unfolding resume_pending_gate_entry_rel_def Let_def by blast

lemma resume_pending_gate_role_family_dbD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows
    "rps_generic_family S (abi_list_ptr (sr_delayed_b R)) =
       sa_delayed_b a"
  using rel
  unfolding resume_pending_gate_entry_rel_def Let_def by blast

lemma resume_pending_gate_role_family_suspD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows
    "rps_generic_family S (abi_list_ptr (sr_suspended R)) =
       sa_suspended a"
  using rel
  unfolding resume_pending_gate_entry_rel_def Let_def by blast

lemma resume_pending_gate_role_rootsD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows
    "abi_list_ptr (sr_delayed_a R) \<in> rpc_generic_roots C \<and>
     abi_list_ptr (sr_delayed_b R) \<in> rpc_generic_roots C \<and>
     abi_list_ptr (sr_suspended R) \<in> rpc_generic_roots C"
  using rel
  unfolding resume_pending_gate_entry_rel_def Let_def by blast

lemma resume_pending_gate_owner_in_rolesD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and pending_u: "u \<in> set (rpc_tasks C)"
  shows
    "rpc_generic_owner C u \<in>
       {abi_list_ptr (sr_delayed_a R), abi_list_ptr (sr_delayed_b R),
        abi_list_ptr (sr_suspended R)}"
  using rel pending_u
  unfolding resume_pending_gate_entry_rel_def Let_def by blast

theorem resume_pending_gate_captured_keyD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows "pending_generic_key_abs t a = rpc_K_G C t"
proof -
  note fam_da = resume_pending_gate_role_family_daD[OF rel]
  note fam_db = resume_pending_gate_role_family_dbD[OF rel]
  note fam_susp = resume_pending_gate_role_family_suspD[OF rel]
  note role_roots = resume_pending_gate_role_rootsD[OF rel]
  have pure: "resume_pending_entry_rel C S"
    by (rule resume_pending_gate_pure_entryD[OF rel])
  have t_pending: "t \<in> set (rpc_tasks C)"
    using tasks by simp
  note old = resume_pending_entry_taskD[OF pure t_pending]
  have entry_key:
    "item_key (rps_generic_family S (rpc_generic_owner C t))
       (Generic t) = rpc_K_G C t"
    using old by blast
  note located = core_wf_pending_generic_key_has_physical_source[
    OF resume_pending_gate_core_wfD[OF rel]
      resume_pending_gate_head_pending_absD[OF rel tasks]]
  show ?thesis
  proof (cases "Generic t \<in> set (ring (sa_delayed_a a))")
    case True
    have root_in:
      "abi_list_ptr (sr_delayed_a R) \<in> rpc_generic_roots C"
      using role_roots by blast
    have mem_S:
      "Generic t \<in> set (ring (rps_generic_family S
         (abi_list_ptr (sr_delayed_a R))))"
      using True fam_da by simp
    have owner_is:
      "rpc_generic_owner C t = abi_list_ptr (sr_delayed_a R)"
      using resume_pending_entry_uniqueD[OF pure tasks root_in] mem_S
      by simp
    have key_here:
      "pending_generic_key_abs t a =
         item_key (sa_delayed_a a) (Generic t)"
      using True by (simp add: pending_generic_key_abs_def)
    show ?thesis
      using key_here entry_key owner_is fam_da by simp
  next
    case False_a: False
    show ?thesis
    proof (cases "Generic t \<in> set (ring (sa_delayed_b a))")
      case True
      have root_in:
        "abi_list_ptr (sr_delayed_b R) \<in> rpc_generic_roots C"
        using role_roots by blast
      have mem_S:
        "Generic t \<in> set (ring (rps_generic_family S
           (abi_list_ptr (sr_delayed_b R))))"
        using True fam_db by simp
      have owner_is:
        "rpc_generic_owner C t = abi_list_ptr (sr_delayed_b R)"
        using resume_pending_entry_uniqueD[OF pure tasks root_in] mem_S
        by simp
      have key_here:
        "pending_generic_key_abs t a =
           item_key (sa_delayed_b a) (Generic t)"
        using False_a True by (simp add: pending_generic_key_abs_def)
      show ?thesis
        using key_here entry_key owner_is fam_db by simp
    next
      case False_b: False
      have in_susp: "Generic t \<in> set (ring (sa_suspended a))"
        using located False_a False_b by blast
      have root_in:
        "abi_list_ptr (sr_suspended R) \<in> rpc_generic_roots C"
        using role_roots by blast
      have mem_S:
        "Generic t \<in> set (ring (rps_generic_family S
           (abi_list_ptr (sr_suspended R))))"
        using in_susp fam_susp by simp
      have owner_is:
        "rpc_generic_owner C t = abi_list_ptr (sr_suspended R)"
        using resume_pending_entry_uniqueD[OF pure tasks root_in] mem_S
        by simp
      have key_here:
        "pending_generic_key_abs t a =
           item_key (sa_suspended a) (Generic t)"
        using False_a False_b
        by (simp add: pending_generic_key_abs_def)
      show ?thesis
        using key_here entry_key owner_is fam_susp by simp
    qed
  qed
qed

section \<open>Task observation against the drained abstract state\<close>

lemma TaskObservationRel_resume_one_transport:
  assumes obs: "TaskObservationRel D h a"
  shows "TaskObservationRel D h (resume_one_pending_abs t a)"
proof -
  have live_eq:
    "sa_live (resume_one_pending_abs t a) = sa_live a"
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def
        resume_add_ready_with_key_abs_def Let_def)
  have pri_eq:
    "sa_priority (resume_one_pending_abs t a) = sa_priority a"
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def
        resume_add_ready_with_key_abs_def Let_def)
  show ?thesis
    using obs
    by (simp add: TaskObservationRel_def live_eq pri_eq)
qed

theorem resume_pending_drained_observation_absD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
       (resume_one_pending_abs t a)"
  by (rule TaskObservationRel_resume_one_transport[
    OF resume_pending_drained_task_observation[OF rel tasks]])

end
