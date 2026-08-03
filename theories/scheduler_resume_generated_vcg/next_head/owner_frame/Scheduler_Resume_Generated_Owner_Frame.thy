theory Scheduler_Resume_Generated_Owner_Frame
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Yield_Join.Scheduler_Resume_Generated_Yield_Join"
begin

text \<open>
  The generated removal rewrites the neighbours' link fields, the removed
  node's container, and the root's count and cursor.  It never writes any
  node's owner field.  The existing sibling frames cover nodes outside the
  target ring; the next pending head, however, stays a member of the very
  ring being shortened, so its whole-item region intersects the write
  footprint.  This theory adds the missing field-precise fact: the owner
  field bytes of every ring member -- including the removed node itself and
  the unlinked head's immediate neighbours -- survive the exact removal
  footprint.
\<close>

section \<open>Intra-item field disjointness\<close>

lemma raw_same_item_prev_owner_disjoint:
  "raw_pointer_field_region (raw_previous_field_ptr u) \<inter>
   raw_owner_field_region u = {}"
proof -
  have separate:
    "{ptr_val u + of_nat 8..+4} \<inter> {ptr_val u + of_nat 12..+4} = {}"
    by (subst intvl_disj_offset; rule intvl_disjoint1; simp)
  show ?thesis
    using separate
    unfolding raw_pointer_field_region_def raw_previous_field_ptr_def
      raw_owner_field_region_def raw_owner_field_ptr_def
    by (simp add: field_lvalue_def xLIST_ITEM_C_pxPrevious_C_fl
        xLIST_ITEM_C_pvOwner_C_fl size_of_def)
qed

lemma raw_same_item_next_owner_disjoint:
  "raw_pointer_field_region (raw_next_field_ptr u) \<inter>
   raw_owner_field_region u = {}"
proof -
  have separate:
    "{ptr_val u + of_nat 4..+4} \<inter> {ptr_val u + of_nat 12..+4} = {}"
    by (subst intvl_disj_offset; rule intvl_disjoint1; simp)
  show ?thesis
    using separate
    unfolding raw_pointer_field_region_def raw_next_field_ptr_def
      raw_owner_field_region_def raw_owner_field_ptr_def
    by (simp add: field_lvalue_def xLIST_ITEM_C_pxNext_C_fl
        xLIST_ITEM_C_pvOwner_C_fl size_of_def)
qed

lemma raw_same_item_container_owner_disjoint:
  "raw_container_field_region u \<inter> raw_owner_field_region u = {}"
proof -
  have separate:
    "{ptr_val u + of_nat 12..+4} \<inter> {ptr_val u + of_nat 16..+4} = {}"
    by (subst intvl_disj_offset; rule intvl_disjoint1; simp)
  show ?thesis
    using separate
    unfolding raw_container_field_region_def raw_container_field_ptr_def
      raw_owner_field_region_def raw_owner_field_ptr_def
    by (auto simp: field_lvalue_def xLIST_ITEM_C_pvContainer_C_fl
        xLIST_ITEM_C_pvOwner_C_fl size_of_def)
qed

section \<open>Owner bytes of ring members survive the exact removal\<close>

lemma raw_remove_member_owner_byte_frame:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
    and q_member: "q \<in> set (ring xs)"
  shows
    "\<forall>a\<in>raw_owner_field_region q.
       raw_remove_concrete_heap h p a = h a"
proof -
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have p_not_end: "p \<noteq> raw_end_item lp"
    using layout member by (auto simp: raw_xlist_layout_def)
  have p_cycle: "p \<in> insert (raw_end_item lp) (set (ring xs))"
    using member by simp
  have next_cycle:
    "xLIST_ITEM_C.pxNext_C (h_val h p) \<in>
       insert (raw_end_item lp) (set (ring xs))"
    using raw_ring_links_next_closed[OF links p_cycle]
    by (simp add: raw_next_at_def p_not_end)
  have previous_cycle:
    "xLIST_ITEM_C.pxPrevious_C (h_val h p) \<in>
       insert (raw_end_item lp) (set (ring xs))"
    using raw_ring_links_prev_closed[OF links p_cycle]
    by (simp add: raw_prev_at_def p_not_end)
  have owner_item: "raw_owner_field_region q \<subseteq> raw_item_region q"
    by (rule raw_owner_field_region_subset_item)
  have q_list: "raw_item_region q \<inter> raw_list_region lp = {}"
    using layout q_member by (auto simp: raw_xlist_layout_def)

  have F1:
    "raw_pointer_field_region
       (raw_previous_field_ptr (xLIST_ITEM_C.pxNext_C (h_val h p))) \<inter>
     raw_owner_field_region q = {}"
  proof (cases "xLIST_ITEM_C.pxNext_C (h_val h p) = q")
    case True
    show ?thesis
      using raw_same_item_prev_owner_disjoint[where u=q] True by simp
  next
    case False
    show ?thesis
      using raw_cycle_previous_field_disjoint_from_other_item[
        OF layout q_member next_cycle False] owner_item by blast
  qed

  have F2:
    "raw_pointer_field_region
       (raw_next_field_ptr (xLIST_ITEM_C.pxPrevious_C (h_val h p))) \<inter>
     raw_owner_field_region q = {}"
  proof (cases "xLIST_ITEM_C.pxPrevious_C (h_val h p) = q")
    case True
    show ?thesis
      using raw_same_item_next_owner_disjoint[where u=q] True by simp
  next
    case False
    show ?thesis
      using raw_cycle_next_field_disjoint_from_other_item[
        OF layout q_member previous_cycle False] owner_item by blast
  qed

  have F3:
    "raw_index_field_region lp \<inter> raw_owner_field_region q = {}"
    using raw_index_field_region_subset_list[where lp=lp]
      q_list owner_item by blast

  have F4:
    "raw_container_field_region p \<inter> raw_owner_field_region q = {}"
  proof (cases "p = q")
    case True
    show ?thesis
      using raw_same_item_container_owner_disjoint[where u=q] True by simp
  next
    case False
    have items:
      "raw_item_region p \<inter> raw_item_region q = {}"
      using layout member q_member False
      by (auto simp: raw_xlist_layout_def)
    show ?thesis
      using raw_container_field_region_subset_item[where p=p]
        items owner_item by blast
  qed

  have F5:
    "raw_count_field_region lp \<inter> raw_owner_field_region q = {}"
    using raw_count_field_region_subset_list[where lp=lp]
      q_list owner_item by blast

  have outside:
    "\<And>a. a \<in> raw_owner_field_region q \<Longrightarrow>
       a \<notin> raw_remove_exact_write_footprint h lp p"
    unfolding raw_remove_exact_write_footprint_def
    using F1 F2 F3 F4 F5 by blast
  show ?thesis
    using raw_remove_concrete_heap_exact_external_frame[OF rel member]
      outside by blast
qed

section \<open>Every pending task is a represented ring member\<close>

lemma resume_pending_gate_pending_liveD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and pending: "u \<in> set (rpc_tasks C)"
  shows "u \<in> rpc_live C"
  using resume_pending_gate_pure_entryD[OF rel] pending
  by (auto simp: resume_pending_entry_rel_def
      resume_pending_context_wf_def)

lemma resume_pending_gate_pending_event_memberD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and pending: "u \<in> set (rpc_tasks C)"
  shows
    "event_item_raw_ptr D u \<in>
       set (ring (event_raw (rpc_pending_root C)))"
proof -
  have live: "u \<in> rpc_live C"
    by (rule resume_pending_gate_pending_liveD[OF rel pending])
  have root: "rpc_pending_root C \<in> rpc_event_roots C"
    using resume_pending_gate_pure_entryD[OF rel]
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_context_wf_def)
  have abstract:
    "Event u \<in>
       set (ring (rps_event_family S (rpc_pending_root C)))"
    using resume_pending_gate_pure_entryD[OF rel] pending
    by (auto simp: resume_pending_entry_rel_def)
  show ?thesis
    using scheduler_event_root_family_member_iff[
      OF resume_pending_gate_event_familyD[OF rel] live root]
      abstract by simp
qed

section \<open>Owner observation survives the generated event removal\<close>

lemma resume_pending_event_remove_owner_frame:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and pending: "u \<in> set (rpc_tasks C)"
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
  have q_member: "?q \<in> set (ring (event_raw ?owner))"
    by (rule resume_pending_gate_pending_event_memberD[OF rel pending])
  have bytes:
    "\<forall>a\<in>raw_owner_field_region ?q.
       raw_remove_concrete_heap ?h ?p a = ?h a"
    by (rule raw_remove_member_owner_byte_frame[
          OF source_rel member q_member])
  have field_same:
    "h_val (raw_remove_concrete_heap ?h ?p) (raw_owner_field_ptr ?q) =
     h_val ?h (raw_owner_field_ptr ?q)"
  proof (rule delay_h_val_region_cong)
    fix address
    assume "address \<in>
      {ptr_val (raw_owner_field_ptr ?q)..+size_of TYPE(unit ptr)}"
    then show
      "raw_remove_concrete_heap ?h ?p address = ?h address"
      using bytes by (simp add: raw_owner_field_region_def)
  qed
  have raw_owner:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val (raw_remove_concrete_heap ?h ?p) ?q) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val ?h ?q)"
    using field_same
    unfolding raw_owner_field_ptr_def
    by (simp only:
      List_V611_Raw_Skip_Translation.xLIST_ITEM_C_h_val_fields(4))
  show ?thesis
    using raw_owner
    unfolding resume_pending_event_remove_heap_def
    by (simp add: event_item_raw_ptr_def abi_event_list_item_ptr_def
        scheduler_event_item_ptr_def flip: abi_item_owner_h_val)
qed

end
