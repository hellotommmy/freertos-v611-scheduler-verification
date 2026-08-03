theory Scheduler_Resume_Generated_Reentry_Gate
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Fam.Scheduler_Resume_Generated_Reentry_Fam"
begin

text \<open>
  Loop re-entry.  The state produced by one checked drain iteration
  satisfies the full gate entry relation again, with the tail context, the
  four-phase snapshot, the drained raw families and the abstract one-task
  resume as witnesses.  Together with the end-to-end body theorem this
  turns the pending-ready loop into a relation-preserving step: gate to
  gate, one task per iteration.
\<close>

theorem resume_pending_gate_reentry:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and roots: "R = generated_scheduler_roots"
  shows
    "resume_pending_gate_entry_rel D R
       (resume_pending_ready_inserted_state D C t generic_raw c)
       (resume_one_pending_abs t a)
       (resume_pending_drained_context C t rest)
       (resume_pending_drained_snapshot C t S)
       (resume_pending_drained_generic_fam C D t c generic_raw)
       (resume_pending_event_raw_after C D t event_raw)"
proof -
  note ctx = resume_pending_drained_context_components[of C t rest]
  have abs_pack:
    "sa_suspend_depth (resume_one_pending_abs t a) =
       sa_suspend_depth a \<and>
     sa_live (resume_one_pending_abs t a) = sa_live a \<and>
     sa_priority (resume_one_pending_abs t a) = sa_priority a \<and>
     sa_current (resume_one_pending_abs t a) = sa_current a"
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def
        resume_add_ready_with_key_abs_def Let_def)

  have h1: "resume_pending_entry_rel
      (resume_pending_drained_context C t rest)
      (resume_pending_drained_snapshot C t S)"
    by (rule resume_pending_drained_entry_rel[
      OF resume_pending_gate_pure_entryD[OF rel] tasks])
  have h2: "core_wf (resume_one_pending_abs t a)"
    by (rule resume_pending_gate_drained_core_wfD[OF rel tasks])
  have h3: "TaskObservationRel D
      (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
        (resume_pending_ready_inserted_state D C t generic_raw c)))
      (resume_one_pending_abs t a)"
    by (rule resume_pending_drained_observation_absD[OF rel tasks])
  have h4: "scheduler_lists_rel D R
      (resume_pending_ready_inserted_state D C t generic_raw c)
      (resume_one_pending_abs t a)"
    by (rule resume_pending_drained_lists_rel[OF rel tasks roots])
  have h5: "scheduler_role_rel R
      (resume_pending_ready_inserted_state D C t generic_raw c)
      (resume_one_pending_abs t a)"
    by (rule resume_pending_drained_role_rel[OF rel tasks roots])
  have h6: "scheduler_scalar_rel
      (resume_pending_ready_inserted_state D C t generic_raw c)
      (resume_one_pending_abs t a)"
    by (rule resume_pending_drained_scalar_rel[OF rel tasks roots])
  have h7: "scheduler_current_rel D
      (resume_pending_ready_inserted_state D C t generic_raw c)
      (resume_one_pending_abs t a)"
    by (rule resume_pending_drained_current_rel[OF rel tasks roots])
  have h8: "sa_suspend_depth (resume_one_pending_abs t a) = 0"
    using abs_pack rel
    unfolding resume_pending_gate_entry_rel_def Let_def by auto
  have h9: "universal_decoder_laws
      (rpc_live (resume_pending_drained_context C t rest)) D"
    using rel ctx
    unfolding resume_pending_gate_entry_rel_def Let_def by auto
  have h10: "rpc_live (resume_pending_drained_context C t rest) =
      sa_live (resume_one_pending_abs t a)"
    using rel ctx abs_pack
    unfolding resume_pending_gate_entry_rel_def Let_def by auto
  have h11:
    "\<forall>u\<in>rpc_live (resume_pending_drained_context C t rest).
       rpc_priority (resume_pending_drained_context C t rest) u =
       sa_priority (resume_one_pending_abs t a) u"
    using rel ctx abs_pack
    unfolding resume_pending_gate_entry_rel_def Let_def by auto
  have h12:
    "rps_event_family (resume_pending_drained_snapshot C t S)
       (rpc_pending_root (resume_pending_drained_context C t rest)) =
     sa_pending (resume_one_pending_abs t a)"
    using reentry_sa_pending_matchL[OF rel tasks roots] ctx by simp
  have h13:
    "rpc_pending_root (resume_pending_drained_context C t rest) =
       abi_list_ptr (sr_pending R)"
    using rel ctx
    unfolding resume_pending_gate_entry_rel_def Let_def by auto
  have h14:
    "\<forall>p<4. abi_list_ptr (sr_ready R p) \<in>
       rpc_generic_roots (resume_pending_drained_context C t rest)"
    using rel ctx
    unfolding resume_pending_gate_entry_rel_def Let_def by auto
  have h15:
    "abi_list_ptr (sr_delayed_a R) \<in>
       rpc_generic_roots (resume_pending_drained_context C t rest)"
    using resume_pending_gate_role_rootsD[OF rel] ctx by simp
  have h16:
    "abi_list_ptr (sr_delayed_b R) \<in>
       rpc_generic_roots (resume_pending_drained_context C t rest)"
    using resume_pending_gate_role_rootsD[OF rel] ctx by simp
  have h17:
    "abi_list_ptr (sr_suspended R) \<in>
       rpc_generic_roots (resume_pending_drained_context C t rest)"
    using resume_pending_gate_role_rootsD[OF rel] ctx by simp
  have h18:
    "\<forall>u\<in>rpc_live (resume_pending_drained_context C t rest).
       rpc_ready_root (resume_pending_drained_context C t rest)
         (rpc_priority (resume_pending_drained_context C t rest) u) =
       abi_list_ptr (sr_ready R
         (rpc_priority (resume_pending_drained_context C t rest) u))"
    using rel ctx
    unfolding resume_pending_gate_entry_rel_def Let_def by auto
  have h19:
    "\<forall>u\<in>set (rpc_tasks
       (resume_pending_drained_context C t rest)).
       rpc_generic_owner (resume_pending_drained_context C t rest) u \<in>
         {abi_list_ptr (sr_delayed_a R), abi_list_ptr (sr_delayed_b R),
          abi_list_ptr (sr_suspended R)}"
  proof
    fix u assume "u \<in> set (rpc_tasks
      (resume_pending_drained_context C t rest))"
    then have u_pending: "u \<in> set (rpc_tasks C)"
      using ctx tasks by simp
    show "rpc_generic_owner (resume_pending_drained_context C t rest) u
        \<in> {abi_list_ptr (sr_delayed_a R),
           abi_list_ptr (sr_delayed_b R),
           abi_list_ptr (sr_suspended R)}"
      using resume_pending_gate_owner_in_rolesD[OF rel u_pending] ctx
      by simp
  qed
  have h20:
    "\<forall>p<4. rps_generic_family
       (resume_pending_drained_snapshot C t S)
       (abi_list_ptr (sr_ready R p)) =
       sa_ready (resume_one_pending_abs t a) p"
    using reentry_sa_ready_matchL[OF rel tasks roots] by auto
  have h21:
    "rps_generic_family (resume_pending_drained_snapshot C t S)
       (abi_list_ptr (sr_delayed_a R)) =
     sa_delayed_a (resume_one_pending_abs t a)"
    using reentry_sa_delayed_a_matchL[OF rel tasks roots] by simp
  have h22:
    "rps_generic_family (resume_pending_drained_snapshot C t S)
       (abi_list_ptr (sr_delayed_b R)) =
     sa_delayed_b (resume_one_pending_abs t a)"
    using reentry_sa_delayed_b_matchL[OF rel tasks roots] by simp
  have h23:
    "rps_generic_family (resume_pending_drained_snapshot C t S)
       (abi_list_ptr (sr_suspended R)) =
     sa_suspended (resume_one_pending_abs t a)"
    using reentry_sa_suspended_matchL[OF rel tasks roots] by simp
  have h24:
    "rpc_entry_top (resume_pending_drained_context C t rest) =
       unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_'
         (resume_pending_ready_inserted_state D C t generic_raw c))"
    using resume_pending_top_raised_semantics[OF rel tasks]
      resume_pending_ready_inserted_top[of D C t generic_raw c] ctx
    by simp
  have h25:
    "\<exists>current\<in>rpc_live
       (resume_pending_drained_context C t rest).
       sa_current (resume_one_pending_abs t a) = Some current \<and>
       rpc_current_priority (resume_pending_drained_context C t rest) =
       rpc_priority (resume_pending_drained_context C t rest) current"
    using rel ctx abs_pack
    unfolding resume_pending_gate_entry_rel_def Let_def by auto

  have h26:
    "scheduler_family_pre_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
       (rpc_generic_roots (resume_pending_drained_context C t rest))
       (resume_pending_drained_generic_fam C D t c generic_raw)
       (rpc_live (resume_pending_drained_context C t rest)) D"
    using resume_pending_drained_generic_family[OF rel tasks] ctx
    by auto
  have h27:
    "\<forall>g\<in>rpc_generic_roots
       (resume_pending_drained_context C t rest).
       set (ring (resume_pending_drained_generic_fam C D t c
         generic_raw g)) \<subseteq>
       resume_pending_generic_raw_set
         (rpc_live (resume_pending_drained_context C t rest)) D"
    using reentry_drained_ring_subsetL[OF rel tasks] ctx by auto
  have h28:
    "\<forall>g\<in>rpc_generic_roots
       (resume_pending_drained_context C t rest).
       xlist_relabel (sd_node_decode D)
         (resume_pending_drained_generic_fam C D t c generic_raw g)
         (rps_generic_family
           (resume_pending_drained_snapshot C t S) g)"
    using resume_pending_drained_generic_relabel[OF rel tasks] ctx
    by (auto simp: resume_pending_drained_snapshot_def)
  have h29:
    "\<forall>u\<in>set (rpc_tasks
       (resume_pending_drained_context C t rest)).
       scheduler_delay_owner_entry_rel
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
           (resume_pending_ready_inserted_state D C t generic_raw c)))
         (rpc_generic_roots (resume_pending_drained_context C t rest))
         (resume_pending_drained_generic_fam C D t c generic_raw)
         (rpc_generic_owner (resume_pending_drained_context C t rest) u)
         (resume_pending_generic_raw_ptr D u) \<and>
       raw_family_insert_geometry
         (rpc_generic_roots (resume_pending_drained_context C t rest))
         (resume_pending_drained_generic_fam C D t c generic_raw)
         (resume_pending_generic_raw_ptr D u)"
  proof
    fix u assume "u \<in> set (rpc_tasks
      (resume_pending_drained_context C t rest))"
    then have u_rest: "u \<in> set rest"
      using ctx by simp
    show "scheduler_delay_owner_entry_rel
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
          (resume_pending_ready_inserted_state D C t generic_raw c)))
        (rpc_generic_roots (resume_pending_drained_context C t rest))
        (resume_pending_drained_generic_fam C D t c generic_raw)
        (rpc_generic_owner (resume_pending_drained_context C t rest) u)
        (resume_pending_generic_raw_ptr D u) \<and>
      raw_family_insert_geometry
        (rpc_generic_roots (resume_pending_drained_context C t rest))
        (resume_pending_drained_generic_fam C D t c generic_raw)
        (resume_pending_generic_raw_ptr D u)"
      using reentry_tail_owner_entryL[OF rel tasks u_rest]
        reentry_tail_geometryL[OF rel tasks u_rest] ctx
      by simp
  qed
  have h30:
    "\<forall>u\<in>rpc_live (resume_pending_drained_context C t rest).
       raw_key_at
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
           (resume_pending_ready_inserted_state D C t generic_raw c)))
         (resume_pending_generic_raw_ptr D u) =
       rpc_K_G (resume_pending_drained_context C t rest) u"
    using resume_pending_drained_keys[OF rel tasks] ctx by auto
  have event_family_eq:
    "rps_event_family (resume_pending_drained_snapshot C t S) =
       rps_event_family (resume_pending_event_unlink_state C t S)"
  proof
    fix e
    show "rps_event_family (resume_pending_drained_snapshot C t S) e =
        rps_event_family (resume_pending_event_unlink_state C t S) e"
      by (simp add: resume_pending_drained_event_at
          resume_pending_event_unlink_state_def)
  qed
  have h31:
    "scheduler_event_root_family_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
       (rpc_event_roots (resume_pending_drained_context C t rest))
       (rpc_pending_root (resume_pending_drained_context C t rest))
       (resume_pending_event_raw_after C D t event_raw)
       (rps_event_family (resume_pending_drained_snapshot C t S))
       (rpc_live (resume_pending_drained_context C t rest))
       (rpc_K_E (resume_pending_drained_context C t rest))"
    using resume_pending_ready_insert_event_family_frame[OF rel tasks]
      ctx event_family_eq
    by simp
  have h32:
    "rpc_generic_roots (resume_pending_drained_context C t rest) \<inter>
       rpc_event_roots (resume_pending_drained_context C t rest) = {}"
    using rel ctx
    unfolding resume_pending_gate_entry_rel_def Let_def by auto
  have h33:
    "\<forall>g\<in>rpc_generic_roots
       (resume_pending_drained_context C t rest).
     \<forall>e\<in>rpc_event_roots
       (resume_pending_drained_context C t rest).
       raw_xlist_storage g
         (resume_pending_drained_generic_fam C D t c generic_raw g) \<inter>
       raw_xlist_storage e
         (resume_pending_event_raw_after C D t event_raw e) = {}"
    using reentry_drained_crossL[OF rel tasks] ctx by auto

  show ?thesis
    unfolding resume_pending_gate_entry_rel_def Let_def
    using h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
      h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33
    by (intro conjI) blast+
qed

end
