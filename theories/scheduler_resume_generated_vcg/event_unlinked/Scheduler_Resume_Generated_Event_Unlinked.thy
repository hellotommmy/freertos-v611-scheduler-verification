theory Scheduler_Resume_Generated_Event_Unlinked
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Source_Factors.Scheduler_Resume_Generated_Source_Factors"
    "EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Preservation.Scheduler_Event_Root_Family_Remove_Preservation"
begin

section \<open>Arbitrary pending-head Event unlink\<close>

definition resume_pending_event_remove_heap ::
  "'tid scheduler_decode \<Rightarrow> 'tid \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> heap_mem"
where
  "resume_pending_event_remove_heap D t c =
     raw_remove_concrete_heap
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (event_item_raw_ptr D t)"

definition resume_pending_event_raw_after ::
  "('tid, xLIST_C ptr) resume_pending_context \<Rightarrow>
   'tid scheduler_decode \<Rightarrow> 'tid \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs)"
where
  "resume_pending_event_raw_after C D t event_raw =
     event_remove_raw_family event_raw (rpc_pending_root C)
       (event_item_raw_ptr D t)"

lemma resume_pending_event_abs_after:
  "event_remove_abs_family (rps_event_family S)
      (rpc_pending_root C) t =
   rps_event_family (resume_pending_event_unlink_state C t S)"
  by (simp add: event_remove_abs_family_def
      resume_pending_event_unlink_state_def)

lemma resume_pending_event_unlinked_phaseD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_loop_phase_inv C S [] (t # rest)
       RP_EventUnlinked (resume_pending_event_unlink_state C t S)"
proof -
  have initial:
    "resume_pending_loop_phase_inv C S [] (rpc_tasks C) RP_LoopHead S"
    by (rule resume_pending_loop_phase_inv_initial[
      OF resume_pending_gate_pure_entryD[OF rel]])
  show ?thesis
    by (rule resume_pending_loop_phase_inv_event_step)
       (use initial tasks in simp)
qed

lemma resume_pending_event_remove_generic_storage_frame:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and root: "g \<in> rpc_generic_roots C"
    and address:
      "address \<in> raw_xlist_storage g (generic_raw g)"
  shows
    "resume_pending_event_remove_heap D t c address =
       hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c) address"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?owner = "rpc_pending_root C"
  let ?p = "event_item_raw_ptr D t"
  have owner_root: "?owner \<in> rpc_event_roots C"
    using resume_pending_gate_pure_entryD[OF rel]
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_context_wf_def)
  have source_rel: "raw_xlist_rel ?h ?owner (event_raw ?owner)"
    by (rule scheduler_event_root_family_raw_rootD[
      OF resume_pending_gate_event_familyD[OF rel] owner_root])
  have member: "?p \<in> set (ring (event_raw ?owner))"
    by (rule resume_pending_gate_head_event_memberD[OF rel tasks])
  have storage_disjoint:
    "raw_xlist_storage g (generic_raw g) \<inter>
       raw_xlist_storage ?owner (event_raw ?owner) = {}"
    using rel root owner_root
    unfolding resume_pending_gate_entry_rel_def Let_def
    by blast
  have footprint:
    "raw_remove_exact_write_footprint ?h ?owner ?p \<subseteq>
       raw_xlist_storage ?owner (event_raw ?owner)"
    by (rule raw_remove_exact_footprint_subset_storage[
      OF source_rel member])
  have outside:
    "address \<notin> raw_remove_exact_write_footprint ?h ?owner ?p"
    using footprint storage_disjoint address by blast
  show ?thesis
    unfolding resume_pending_event_remove_heap_def
    by (rule raw_remove_concrete_heap_exact_external_frame[
      OF source_rel member outside])
qed

lemma resume_pending_event_remove_generic_root_frame:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and root: "g \<in> rpc_generic_roots C"
  shows
    "raw_xlist_rel (resume_pending_event_remove_heap D t c)
       g (generic_raw g)"
proof -
  have old:
    "raw_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       g (generic_raw g)"
    using resume_pending_gate_generic_familyD[OF rel] root
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  show ?thesis
  proof (rule delay_raw_xlist_rel_storage_frame[OF old])
    fix address
    assume "address \<in> raw_xlist_storage g (generic_raw g)"
    then show
      "resume_pending_event_remove_heap D t c address =
       hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c) address"
      by (rule resume_pending_event_remove_generic_storage_frame[
        OF rel tasks root])
  qed
qed

lemma resume_pending_event_remove_generic_family_frame:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "scheduler_family_pre_rel
       (resume_pending_event_remove_heap D t c)
       (rpc_generic_roots C) generic_raw (rpc_live C) D"
proof -
  have old:
    "scheduler_family_pre_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (rpc_generic_roots C) generic_raw (rpc_live C) D"
    by (rule resume_pending_gate_generic_familyD[OF rel])
  have family:
    "raw_family_rel (resume_pending_event_remove_heap D t c)
       (rpc_generic_roots C) generic_raw"
    unfolding raw_family_rel_def
  proof (intro conjI ballI)
    show "finite (rpc_generic_roots C)"
      using old
      by (simp add: scheduler_family_pre_rel_def raw_family_rel_def)
  next
    fix g
    assume "g \<in> rpc_generic_roots C"
    then show
      "raw_xlist_rel (resume_pending_event_remove_heap D t c)
         g (generic_raw g)"
      by (rule resume_pending_event_remove_generic_root_frame[
        OF rel tasks])
  qed
  show ?thesis
    using old family by (simp add: scheduler_family_pre_rel_def)
qed

lemma resume_pending_event_remove_generic_owner_frame:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "scheduler_delay_owner_entry_rel
       (resume_pending_event_remove_heap D t c)
       (rpc_generic_roots C) generic_raw (rpc_generic_owner C t)
       (resume_pending_generic_raw_ptr D t)"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?g = "rpc_generic_owner C t"
  let ?p = "resume_pending_generic_raw_ptr D t"
  have old:
    "scheduler_delay_owner_entry_rel ?h
       (rpc_generic_roots C) generic_raw ?g ?p"
    using resume_pending_gate_head_generic_ownerD[OF rel tasks] by blast
  have root: "?g \<in> rpc_generic_roots C"
    using old by (simp add: scheduler_delay_owner_entry_rel_def)
  have member: "?p \<in> set (ring (generic_raw ?g))"
    by (rule scheduler_delay_owner_entry_member[OF old])
  have item_same:
    "h_val (resume_pending_event_remove_heap D t c) ?p = h_val ?h ?p"
  proof (rule delay_h_val_region_cong)
    fix address
    assume address: "address \<in> {ptr_val ?p..+size_of TYPE(xLIST_ITEM_C)}"
    have storage:
      "address \<in> raw_xlist_storage ?g (generic_raw ?g)"
      using member address
      by (auto simp: raw_xlist_storage_def raw_item_region_def)
    show "resume_pending_event_remove_heap D t c address = ?h address"
      by (rule resume_pending_event_remove_generic_storage_frame[
        OF rel tasks root storage])
  qed
  show ?thesis
    using old item_same
    by (simp add: scheduler_delay_owner_entry_rel_def)
qed

lemma resume_pending_event_remove_generic_item_frame:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and live: "u \<in> rpc_live C"
  shows
    "h_val (resume_pending_event_remove_heap D t c)
       (resume_pending_generic_raw_ptr D u) =
     h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (resume_pending_generic_raw_ptr D u)"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?owner = "rpc_pending_root C"
  let ?p = "event_item_raw_ptr D t"
  let ?q = "resume_pending_generic_raw_ptr D u"
  have owner_root: "?owner \<in> rpc_event_roots C"
    using resume_pending_gate_pure_entryD[OF rel]
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_context_wf_def)
  have head_live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  have member: "?p \<in> set (ring (event_raw ?owner))"
    by (rule resume_pending_gate_head_event_memberD[OF rel tasks])
  have managed: "?q \<in> universal_managed_nodes (rpc_live C) D"
    using live
    by (auto simp: resume_pending_generic_raw_ptr_def
        universal_managed_nodes_def)
  have nonmember: "?q \<notin> set (ring (event_raw ?owner))"
    by (rule resume_pending_gate_generic_notin_event_rootD[
      OF rel live owner_root])
  have bytes:
    "\<forall>address\<in>raw_item_region ?q.
       raw_remove_concrete_heap ?h ?p address = ?h address"
    using raw_remove_family_sibling_item_priority_byte_frame[
      OF scheduler_event_root_family_preD[
        OF resume_pending_gate_event_familyD[OF rel]]
      owner_root member managed nonmember head_live]
    by blast
  show ?thesis
    unfolding resume_pending_event_remove_heap_def
  proof (rule delay_h_val_region_cong)
    fix address
    assume "address \<in> {ptr_val ?q..+size_of TYPE(xLIST_ITEM_C)}"
    then show "raw_remove_concrete_heap ?h ?p address = ?h address"
      using bytes by (simp add: raw_item_region_def)
  qed
qed

lemma resume_pending_event_remove_generic_keys_frame:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and live: "u \<in> rpc_live C"
  shows
    "raw_key_at (resume_pending_event_remove_heap D t c)
       (resume_pending_generic_raw_ptr D u) = rpc_K_G C u"
proof -
  have old:
    "raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (resume_pending_generic_raw_ptr D u) = rpc_K_G C u"
    using rel live
    unfolding resume_pending_gate_entry_rel_def Let_def
    by blast
  show ?thesis
    using resume_pending_event_remove_generic_item_frame[
      OF rel tasks live] old
    by (simp add: raw_key_at_def)
qed

lemma resume_pending_event_remove_priority_frame:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and live: "u \<in> rpc_live C"
  shows
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (resume_pending_event_remove_heap D t c)
         (sd_tcb_ptr D u)) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (sd_tcb_ptr D u))"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?owner = "rpc_pending_root C"
  let ?p = "event_item_raw_ptr D t"
  let ?tp = "sd_tcb_ptr D u"
  let ?q = "resume_pending_generic_raw_ptr D u"
  have owner_root: "?owner \<in> rpc_event_roots C"
    using resume_pending_gate_pure_entryD[OF rel]
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_context_wf_def)
  have member: "?p \<in> set (ring (event_raw ?owner))"
    by (rule resume_pending_gate_head_event_memberD[OF rel tasks])
  have managed: "?q \<in> universal_managed_nodes (rpc_live C) D"
    using live
    by (auto simp: resume_pending_generic_raw_ptr_def
        universal_managed_nodes_def)
  have nonmember: "?q \<notin> set (ring (event_raw ?owner))"
    by (rule resume_pending_gate_generic_notin_event_rootD[
      OF rel live owner_root])
  have bytes:
    "\<forall>address\<in>universal_priority_field_region ?tp.
       raw_remove_concrete_heap ?h ?p address = ?h address"
    using raw_remove_family_sibling_item_priority_byte_frame[
      OF scheduler_event_root_family_preD[
        OF resume_pending_gate_event_familyD[OF rel]]
      owner_root member managed nonmember live]
    by blast
  have field_same:
    "h_val (raw_remove_concrete_heap ?h ?p)
       (universal_priority_field_ptr ?tp) =
     h_val ?h (universal_priority_field_ptr ?tp)"
  proof (rule delay_h_val_region_cong)
    fix address
    assume "address \<in>
      {ptr_val (universal_priority_field_ptr ?tp)..+size_of TYPE(32 word)}"
    then show "raw_remove_concrete_heap ?h ?p address = ?h address"
      using bytes by (simp add: universal_priority_field_region_def)
  qed
  show ?thesis
    using field_same
    unfolding resume_pending_event_remove_heap_def
      universal_priority_field_ptr_def
    by (simp only:
      Scheduler_V611_Parse.tskTaskControlBlock_C_h_val_fields(4))
qed

lemma resume_pending_event_remove_family_post:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "scheduler_event_root_family_rel D
       (resume_pending_event_remove_heap D t c)
       (rpc_event_roots C) (rpc_pending_root C)
       (resume_pending_event_raw_after C D t event_raw)
       (rps_event_family (resume_pending_event_unlink_state C t S))
       (rpc_live C) (rpc_K_E C) \<and>
     pvContainer_C
       (h_val (resume_pending_event_remove_heap D t c)
         (event_item_raw_ptr D t)) = NULL \<and>
     raw_key_at (resume_pending_event_remove_heap D t c)
       (event_item_raw_ptr D t) = rpc_K_E C t \<and>
     raw_family_members (rpc_event_roots C)
       (resume_pending_event_raw_after C D t event_raw)
       (event_item_raw_ptr D t) = {}"
proof -
  have owner: "rpc_pending_root C \<in> rpc_event_roots C"
    using resume_pending_gate_pure_entryD[OF rel]
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_context_wf_def)
  have live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  have member:
    "event_item_raw_ptr D t \<in>
       set (ring (event_raw (rpc_pending_root C)))"
    by (rule resume_pending_gate_head_event_memberD[OF rel tasks])
  note post = scheduler_event_root_family_remove_post_observations[
    OF resume_pending_gate_event_familyD[OF rel] owner live member]
  show ?thesis
    using post
    by (simp add: resume_pending_event_remove_heap_def
        resume_pending_event_raw_after_def resume_pending_event_abs_after)
qed

theorem resume_pending_generated_event_unlinked_cutpoint:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "Scheduler_V611_Delay_Translation.vListRemove'
       (scheduler_event_item_ptr (sd_tcb_ptr D t)) \<bullet> c
     \<lbrace>\<lambda>r s.
       r = Result () \<and>
       s = scheduler_mem_state
         (resume_pending_event_remove_heap D t c) c \<and>
       scheduler_event_root_family_rel D
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
         (rpc_event_roots C) (rpc_pending_root C)
         (resume_pending_event_raw_after C D t event_raw)
         (rps_event_family (resume_pending_event_unlink_state C t S))
         (rpc_live C) (rpc_K_E C) \<and>
       scheduler_family_pre_rel
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
         (rpc_generic_roots C) generic_raw (rpc_live C) D \<and>
       scheduler_delay_owner_entry_rel
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
         (rpc_generic_roots C) generic_raw (rpc_generic_owner C t)
         (resume_pending_generic_raw_ptr D t) \<and>
       pvContainer_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
           (event_item_raw_ptr D t)) = NULL \<and>
       raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
         (event_item_raw_ptr D t) = rpc_K_E C t \<and>
       raw_family_members (rpc_event_roots C)
         (resume_pending_event_raw_after C D t event_raw)
         (event_item_raw_ptr D t) = {} \<and>
       resume_pending_loop_phase_inv C S [] (t # rest)
         RP_EventUnlinked (resume_pending_event_unlink_state C t S)
     \<rbrace>"
proof -
  note source = resume_pending_head_event_remove_generated_leaf[OF rel tasks]
  note event = resume_pending_event_remove_family_post[OF rel tasks]
  note generic = resume_pending_event_remove_generic_family_frame[OF rel tasks]
  note owner = resume_pending_event_remove_generic_owner_frame[OF rel tasks]
  note phase = resume_pending_event_unlinked_phaseD[OF rel tasks]
  show ?thesis
    apply (rule runs_to_weaken[OF source])
    using event generic owner phase
    by (auto simp: resume_pending_event_remove_heap_def
        event_item_raw_ptr_def scheduler_event_item_ptr_def
        abi_event_list_item_ptr_def)
qed

text \<open>
  The head task, the remaining list, both root universes, every key and every
  heap byte remain arbitrary.  This theorem is the real first destructive
  cutpoint of the generated pending-ready loop.  It deliberately records a
  transient EventUnlinked phase; it does not pretend that core_wf already
  holds before the same task's Generic item is reinserted into a ready list.
\<close>

end
