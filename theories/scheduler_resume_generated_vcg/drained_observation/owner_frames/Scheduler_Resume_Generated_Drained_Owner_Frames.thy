theory Scheduler_Resume_Generated_Drained_Owner_Frames
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Insert_Owner_Frame.Scheduler_Resume_Generated_Insert_Owner_Frame"
begin

text \<open>
  Re-establishing the task observation relation at the drained state needs
  the owner field of both embedded items of every live task -- not only the
  pending members -- to survive all three heap writes of the drain body.
  This theory proves those owner projections heap by heap.  Each lemma
  covers an arbitrary live task: members of the rewritten rings go through
  the field-precise member frames, and non-members through the sibling item
  frames; neither case fixes any task, priority or topology.
\<close>

section \<open>Owner bytes to owner projections\<close>

lemma raw_owner_bytes_to_projection:
  assumes bytes: "\<forall>a\<in>raw_owner_field_region q. h' a = h a"
  shows
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h' q) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h q)"
proof -
  have field_same:
    "h_val h' (raw_owner_field_ptr q) = h_val h (raw_owner_field_ptr q)"
  proof (rule delay_h_val_region_cong)
    fix address
    assume "address \<in>
      {ptr_val (raw_owner_field_ptr q)..+size_of TYPE(unit ptr)}"
    then show "h' address = h address"
      using bytes by (simp add: raw_owner_field_region_def)
  qed
  show ?thesis
    using field_same
    unfolding raw_owner_field_ptr_def
    by (simp only:
      List_V611_Raw_Skip_Translation.xLIST_ITEM_C_h_val_fields(4))
qed

lemma resume_pending_event_owner_projection_transport:
  assumes proj:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h' (event_item_raw_ptr D u)) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h (event_item_raw_ptr D u))"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h' (scheduler_event_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D u)))"
  using proj
  by (simp add: event_item_raw_ptr_def abi_event_list_item_ptr_def
      scheduler_event_item_ptr_def flip: abi_item_owner_h_val)

lemma resume_pending_generic_owner_projection_transport:
  assumes proj:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h' (resume_pending_generic_raw_ptr D u)) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h (resume_pending_generic_raw_ptr D u))"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h' (scheduler_generic_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h (scheduler_generic_item_ptr (sd_tcb_ptr D u)))"
  using proj
  by (simp add: resume_pending_generic_raw_ptr_def
      abi_generic_list_item_ptr_def scheduler_generic_item_ptr_def
      flip: abi_item_owner_h_val)

section \<open>Event-item owner across the generated event removal\<close>

lemma resume_pending_event_remove_event_owner_live:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and live: "u \<in> rpc_live C"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (resume_pending_event_remove_heap D t c)
         (scheduler_event_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (scheduler_event_item_ptr (sd_tcb_ptr D u)))"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?owner = "rpc_pending_root C"
  let ?p = "event_item_raw_ptr D t"
  let ?q = "event_item_raw_ptr D u"
  have root: "?owner \<in> rpc_event_roots C"
    using resume_pending_gate_pure_entryD[OF rel]
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_context_wf_def)
  have source_rel: "raw_xlist_rel ?h ?owner (event_raw ?owner)"
    by (rule scheduler_event_root_family_raw_rootD[
      OF resume_pending_gate_event_familyD[OF rel] root])
  have member: "?p \<in> set (ring (event_raw ?owner))"
    by (rule resume_pending_gate_head_event_memberD[OF rel tasks])
  have bytes:
    "\<forall>a\<in>raw_owner_field_region ?q.
       raw_remove_concrete_heap ?h ?p a = ?h a"
  proof (cases "?q \<in> set (ring (event_raw ?owner))")
    case True
    show ?thesis
      by (rule raw_remove_member_owner_byte_frame[
        OF source_rel member True])
  next
    case False
    have pre_event:
      "scheduler_family_pre_rel ?h (rpc_event_roots C) event_raw
         (rpc_live C) D"
      by (rule scheduler_event_root_family_preD[
        OF resume_pending_gate_event_familyD[OF rel]])
    have q_managed: "?q \<in> universal_managed_nodes (rpc_live C) D"
      using live
      by (auto simp: event_item_raw_ptr_def universal_managed_nodes_def)
    have item_bytes:
      "\<forall>a\<in>raw_item_region ?q.
         raw_remove_concrete_heap ?h ?p a = ?h a"
      using raw_remove_family_sibling_item_priority_byte_frame[
        OF pre_event root member q_managed False live]
      by blast
    show ?thesis
      using item_bytes raw_owner_field_region_subset_item[where p="?q"]
      by blast
  qed
  show ?thesis
    unfolding resume_pending_event_remove_heap_def
    by (rule resume_pending_event_owner_projection_transport[
      OF raw_owner_bytes_to_projection[OF bytes]])
qed

section \<open>Generic-item owner across the generated event removal\<close>

lemma resume_pending_event_remove_generic_owner_live:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and live: "u \<in> rpc_live C"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (resume_pending_event_remove_heap D t c)
         (scheduler_generic_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (scheduler_generic_item_ptr (sd_tcb_ptr D u)))"
proof -
  have whole:
    "h_val (resume_pending_event_remove_heap D t c)
       (resume_pending_generic_raw_ptr D u) =
     h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (resume_pending_generic_raw_ptr D u)"
    by (rule resume_pending_event_remove_generic_item_frame[
      OF rel tasks live])
  show ?thesis
    by (rule resume_pending_generic_owner_projection_transport)
       (simp add: whole)
qed

section \<open>Generic-item owner across the generated generic removal\<close>

lemma resume_pending_generic_remove_generic_owner_live:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and live: "u \<in> rpc_live C"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (resume_pending_generic_remove_heap D t c)
         (scheduler_generic_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (resume_pending_event_remove_heap D t c)
         (scheduler_generic_item_ptr (sd_tcb_ptr D u)))"
proof -
  let ?hE = "resume_pending_event_remove_heap D t c"
  let ?owner = "rpc_generic_owner C t"
  let ?p = "resume_pending_generic_raw_ptr D t"
  let ?q = "resume_pending_generic_raw_ptr D u"
  have owner_entry:
    "scheduler_delay_owner_entry_rel ?hE (rpc_generic_roots C)
       generic_raw ?owner ?p"
    by (rule resume_pending_event_remove_generic_owner_frame[OF rel tasks])
  have owner_root: "?owner \<in> rpc_generic_roots C"
    using owner_entry by (simp add: scheduler_delay_owner_entry_rel_def)
  have source_rel: "raw_xlist_rel ?hE ?owner (generic_raw ?owner)"
    by (rule resume_pending_event_remove_generic_root_frame[
      OF rel tasks owner_root])
  have member: "?p \<in> set (ring (generic_raw ?owner))"
    by (rule scheduler_delay_owner_entry_member[OF owner_entry])
  have bytes:
    "\<forall>a\<in>raw_owner_field_region ?q.
       raw_remove_concrete_heap ?hE ?p a = ?hE a"
  proof (cases "?q \<in> set (ring (generic_raw ?owner))")
    case True
    show ?thesis
      by (rule raw_remove_member_owner_byte_frame[
        OF source_rel member True])
  next
    case False
    have pre_generic:
      "scheduler_family_pre_rel ?hE (rpc_generic_roots C) generic_raw
         (rpc_live C) D"
      by (rule resume_pending_event_remove_generic_family_frame[
        OF rel tasks])
    have q_managed: "?q \<in> universal_managed_nodes (rpc_live C) D"
      using live
      by (auto simp: resume_pending_generic_raw_ptr_def
          universal_managed_nodes_def)
    have item_bytes:
      "\<forall>a\<in>raw_item_region ?q.
         raw_remove_concrete_heap ?hE ?p a = ?hE a"
      using raw_remove_family_sibling_item_priority_byte_frame[
        OF pre_generic owner_root member q_managed False live]
      by blast
    show ?thesis
      using item_bytes raw_owner_field_region_subset_item[where p="?q"]
      by blast
  qed
  show ?thesis
    unfolding resume_pending_generic_remove_heap_def
    by (rule resume_pending_generic_owner_projection_transport[
      OF raw_owner_bytes_to_projection[OF bytes]])
qed

section \<open>Event-item owner across the generated generic removal\<close>

lemma resume_pending_generic_remove_event_owner_live:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and live: "u \<in> rpc_live C"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (resume_pending_generic_remove_heap D t c)
         (scheduler_event_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (resume_pending_event_remove_heap D t c)
         (scheduler_event_item_ptr (sd_tcb_ptr D u)))"
proof -
  have whole:
    "h_val (resume_pending_generic_remove_heap D t c)
       (event_item_raw_ptr D u) =
     h_val (resume_pending_event_remove_heap D t c)
       (event_item_raw_ptr D u)"
    by (rule resume_pending_generic_remove_event_item_frame[
      OF rel tasks live])
  show ?thesis
    by (rule resume_pending_event_owner_projection_transport)
       (simp add: whole)
qed

section \<open>Both owners across the generated ready insertion\<close>

lemma resume_pending_ready_insert_generic_owner_live:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and live: "u \<in> rpc_live C"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
         (scheduler_generic_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (resume_pending_generic_remove_heap D t c)
         (scheduler_generic_item_ptr (sd_tcb_ptr D u)))"
proof -
  let ?hR = "resume_pending_generic_remove_heap D t c"
  let ?target = "rpc_ready_root C (rpc_priority C t)"
  let ?fam = "resume_pending_generic_raw_after C D t generic_raw"
  let ?p = "resume_pending_generic_raw_ptr D t"
  let ?q = "resume_pending_generic_raw_ptr D u"
  have t_live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  have heap_base:
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
       (resume_pending_top_raised_state D t c)) = ?hR"
    using resume_pending_top_raised_semantics[OF rel tasks] by blast
  have pre:
    "scheduler_family_pre_rel ?hR (rpc_generic_roots C) ?fam
       (rpc_live C) D"
    using resume_pending_top_raised_generic_family[OF rel tasks]
      heap_base by simp
  have target: "?target \<in> rpc_generic_roots C"
    by (rule resume_pending_ready_target_in_roots[OF rel tasks])
  have fresh: "raw_fresh_for_insert ?target (ring (?fam ?target)) ?p"
    by (rule resume_pending_ready_fresh_after_removal[OF rel tasks])
  have p_managed: "?p \<in> universal_managed_nodes (rpc_live C) D"
    using t_live
    by (auto simp: resume_pending_generic_raw_ptr_def
        universal_managed_nodes_def)
  have q_managed: "?q \<in> universal_managed_nodes (rpc_live C) D"
    using live
    by (auto simp: resume_pending_generic_raw_ptr_def
        universal_managed_nodes_def)
  have bytes:
    "\<forall>a\<in>raw_owner_field_region ?q.
       raw_insert_concrete_heap ?hR ?target (?fam ?target) ?p a = ?hR a"
    by (rule raw_insert_end_family_owner_byte_frame[
      OF pre target fresh p_managed q_managed])
  have heap_inserted:
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
       (resume_pending_ready_inserted_state D C t generic_raw c)) =
     raw_insert_concrete_heap ?hR ?target (?fam ?target) ?p"
    using heap_base
    by (simp add: resume_pending_ready_inserted_heap)
  have proj:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val (raw_insert_concrete_heap ?hR ?target (?fam ?target) ?p)
         ?q) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val ?hR ?q)"
    by (rule raw_owner_bytes_to_projection[OF bytes])
  show ?thesis
    using resume_pending_generic_owner_projection_transport[OF proj]
    by (simp add: heap_inserted)
qed

lemma resume_pending_ready_insert_event_owner_live:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and live: "u \<in> rpc_live C"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
         (scheduler_event_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (resume_pending_generic_remove_heap D t c)
         (scheduler_event_item_ptr (sd_tcb_ptr D u)))"
proof -
  have whole:
    "h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
       (resume_pending_ready_inserted_state D C t generic_raw c)))
       (event_item_raw_ptr D u) =
     h_val (resume_pending_generic_remove_heap D t c)
       (event_item_raw_ptr D u)"
    by (rule resume_pending_ready_insert_event_item_frame[
      OF rel tasks live])
  show ?thesis
    by (rule resume_pending_event_owner_projection_transport)
       (simp add: whole)
qed

end
