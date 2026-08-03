theory Scheduler_Resume_Generated_Container_Frame
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Pure.Scheduler_Resume_Generated_Reentry_Pure"
begin

text \<open>
  The gate's owner-entry clause records each remaining pending task's
  container field.  The insertion writes exactly one container -- the
  awakened item's -- so every other managed node's container bytes survive.
  This is the container analogue of the owner and key frames; together with
  the removal preservation's container clause it carries the owner-entry
  observations of the tail tasks to the drained heap.
\<close>

section \<open>Intra-item disjointness for the container field\<close>

lemma raw_same_item_next_container_disjoint:
  "raw_pointer_field_region (raw_next_field_ptr u) \<inter>
   raw_container_field_region u = {}"
proof -
  have separate:
    "{ptr_val u + of_nat 4..+4} \<inter> {ptr_val u + of_nat 16..+4} = {}"
    by (subst intvl_disj_offset; rule intvl_disjoint1; simp)
  show ?thesis
    using separate
    unfolding raw_pointer_field_region_def raw_next_field_ptr_def
      raw_container_field_region_def raw_container_field_ptr_def
    by (auto simp: field_lvalue_def xLIST_ITEM_C_pxNext_C_fl
        xLIST_ITEM_C_pvContainer_C_fl size_of_def)
qed

lemma raw_same_item_prev_container_disjoint:
  "raw_pointer_field_region (raw_previous_field_ptr u) \<inter>
   raw_container_field_region u = {}"
proof -
  have separate:
    "{ptr_val u + of_nat 8..+4} \<inter> {ptr_val u + of_nat 16..+4} = {}"
    by (subst intvl_disj_offset; rule intvl_disjoint1; simp)
  show ?thesis
    using separate
    unfolding raw_pointer_field_region_def raw_previous_field_ptr_def
      raw_container_field_region_def raw_container_field_ptr_def
    by (auto simp: field_lvalue_def xLIST_ITEM_C_pxPrevious_C_fl
        xLIST_ITEM_C_pvContainer_C_fl size_of_def)
qed

section \<open>Container region against the insert footprint\<close>

lemma raw_managed_next_field_container_disjoint:
  assumes geometry: "universal_tcb_geometry live D"
    and u_managed: "u \<in> universal_managed_nodes live D"
    and w_managed: "w \<in> universal_managed_nodes live D"
  shows
    "raw_pointer_field_region (raw_next_field_ptr u) \<inter>
     raw_container_field_region w = {}"
proof (cases "u = w")
  case True
  show ?thesis
    using raw_same_item_next_container_disjoint[where u=w] True by simp
next
  case False
  have items: "raw_item_region u \<inter> raw_item_region w = {}"
    by (rule universal_distinct_managed_item_regions_disjoint[
      OF geometry u_managed w_managed False])
  show ?thesis
    using raw_next_field_region_subset_item[where u=u]
      raw_container_field_region_subset_item[where p=w] items by blast
qed

lemma raw_managed_prev_field_container_disjoint:
  assumes geometry: "universal_tcb_geometry live D"
    and u_managed: "u \<in> universal_managed_nodes live D"
    and w_managed: "w \<in> universal_managed_nodes live D"
  shows
    "raw_pointer_field_region (raw_previous_field_ptr u) \<inter>
     raw_container_field_region w = {}"
proof (cases "u = w")
  case True
  show ?thesis
    using raw_same_item_prev_container_disjoint[where u=w] True by simp
next
  case False
  have items: "raw_item_region u \<inter> raw_item_region w = {}"
    by (rule universal_distinct_managed_item_regions_disjoint[
      OF geometry u_managed w_managed False])
  show ?thesis
    using raw_previous_field_region_subset_item[where u=u]
      raw_container_field_region_subset_item[where p=w] items by blast
qed

theorem raw_insert_end_family_container_byte_frame:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and fresh: "raw_fresh_for_insert target (ring (fam target)) p"
    and p_managed: "p \<in> universal_managed_nodes live D"
    and w_managed: "w \<in> universal_managed_nodes live D"
    and w_ne_p: "w \<noteq> p"
  shows
    "\<forall>a\<in>raw_container_field_region w.
       raw_insert_concrete_heap h target (fam target) p a = h a"
proof -
  let ?c = "raw_cursor_node target (fam target)"
  let ?q = "raw_next_at h target ?c"
  have geometry: "universal_tcb_geometry live D"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have rel: "raw_xlist_rel h target (fam target)"
    using pre target
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have wf: "xlist_wf (fam target)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have links: "raw_ring_links h target (ring (fam target))"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have c_cycle:
    "?c \<in> insert (raw_end_item target) (set (ring (fam target)))"
    by (rule raw_cursor_node_in_cycle[OF wf])
  have q_cycle:
    "?q \<in> insert (raw_end_item target) (set (ring (fam target)))"
    by (rule raw_ring_links_next_closed[OF links c_cycle])
  have root_item:
    "raw_list_region target \<inter> raw_item_region w = {}"
    by (rule scheduler_family_root_managed_item_disjoint[
      OF pre target w_managed])
  have F1:
    "raw_pointer_field_region (raw_next_field_ptr p) \<inter>
     raw_container_field_region w = {}"
    by (rule raw_managed_next_field_container_disjoint[
      OF geometry p_managed w_managed])
  have F2:
    "raw_pointer_field_region (raw_previous_field_ptr p) \<inter>
     raw_container_field_region w = {}"
    by (rule raw_managed_prev_field_container_disjoint[
      OF geometry p_managed w_managed])
  have cycle_field:
    "\<And>u. u \<in> insert (raw_end_item target)
        (set (ring (fam target))) \<Longrightarrow>
      raw_pointer_field_region (raw_next_field_ptr u) \<inter>
        raw_container_field_region w = {} \<and>
      raw_pointer_field_region (raw_previous_field_ptr u) \<inter>
        raw_container_field_region w = {}"
  proof -
    fix u
    assume u_cycle:
      "u \<in> insert (raw_end_item target) (set (ring (fam target)))"
    show "?thesis u"
    proof (cases "u = raw_end_item target")
      case True
      show ?thesis
        using raw_end_next_field_region_subset_list[where lp=target]
          raw_end_previous_field_region_subset_list[where lp=target]
          raw_container_field_region_subset_item[where p=w]
          root_item True
        by blast
    next
      case False
      have ring_managed:
        "set (ring (fam target)) \<subseteq> universal_managed_nodes live D"
        using pre target by (auto simp: scheduler_family_pre_rel_def)
      have u_managed: "u \<in> universal_managed_nodes live D"
        using u_cycle False ring_managed by auto
      show ?thesis
        using raw_managed_next_field_container_disjoint[
            OF geometry u_managed w_managed]
          raw_managed_prev_field_container_disjoint[
            OF geometry u_managed w_managed]
        by blast
    qed
  qed
  have F3:
    "raw_pointer_field_region (raw_previous_field_ptr ?q) \<inter>
     raw_container_field_region w = {}"
    using cycle_field[OF q_cycle] by blast
  have F4:
    "raw_pointer_field_region (raw_next_field_ptr ?c) \<inter>
     raw_container_field_region w = {}"
    using cycle_field[OF c_cycle] by blast
  have F5:
    "raw_index_field_region target \<inter>
     raw_container_field_region w = {}"
    using raw_index_field_region_subset_list[where lp=target]
      raw_container_field_region_subset_item[where p=w] root_item
    by blast
  have F6:
    "raw_container_field_region p \<inter>
     raw_container_field_region w = {}"
  proof -
    have items: "raw_item_region p \<inter> raw_item_region w = {}"
      by (rule universal_distinct_managed_item_regions_disjoint[
        OF geometry p_managed w_managed w_ne_p[symmetric]])
    show ?thesis
      using raw_container_field_region_subset_item[where p=p]
        raw_container_field_region_subset_item[where p=w] items
      by blast
  qed
  have F7:
    "raw_count_field_region target \<inter>
     raw_container_field_region w = {}"
    using raw_count_field_region_subset_list[where lp=target]
      raw_container_field_region_subset_item[where p=w] root_item
    by blast
  have outside:
    "\<And>a. a \<in> raw_container_field_region w \<Longrightarrow>
       a \<notin> raw_insert_end_exact_write_footprint h target (fam target) p"
    unfolding raw_insert_end_exact_write_footprint_def Let_def
    using F1 F2 F3 F4 F5 F6 F7 by blast
  show ?thesis
    using raw_insert_concrete_heap_exact_external_frame[OF rel fresh]
      outside by blast
qed

section \<open>Container bytes to container projections\<close>

lemma raw_container_bytes_to_projection:
  assumes bytes: "\<forall>a\<in>raw_container_field_region q. h' a = h a"
  shows
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
       (h_val h' q) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
       (h_val h q)"
proof -
  have field_same:
    "h_val h' (raw_container_field_ptr q) =
     h_val h (raw_container_field_ptr q)"
  proof (rule delay_h_val_region_cong)
    fix address
    assume "address \<in>
      {ptr_val (raw_container_field_ptr q)..+size_of TYPE(unit ptr)}"
    then show "h' address = h address"
      using bytes by (simp add: raw_container_field_region_def)
  qed
  show ?thesis
    using field_same
    unfolding raw_container_field_ptr_def
    by (simp only:
      List_V611_Raw_Skip_Translation.xLIST_ITEM_C_h_val_fields(5))
qed

section \<open>Tail owner-entry observations at the drained heap\<close>

lemma resume_pending_gate_tail_owner_entryD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and pending_u: "u \<in> set (rpc_tasks C)"
  shows
    "scheduler_delay_owner_entry_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (rpc_generic_roots C) generic_raw (rpc_generic_owner C u)
       (resume_pending_generic_raw_ptr D u)"
  using rel pending_u
  unfolding resume_pending_gate_entry_rel_def Let_def
  by blast

lemma resume_pending_drained_container_observationD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and u_rest: "u \<in> set rest"
  shows
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
         (resume_pending_generic_raw_ptr D u)) =
     PTR_COERCE(xLIST_C \<rightarrow> unit) (rpc_generic_owner C u)"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?hR = "resume_pending_generic_remove_heap D t c"
  let ?target = "rpc_ready_root C (rpc_priority C t)"
  let ?fam = "resume_pending_generic_raw_after C D t generic_raw"
  let ?p = "resume_pending_generic_raw_ptr D t"
  let ?q = "resume_pending_generic_raw_ptr D u"
  have u_pending: "u \<in> set (rpc_tasks C)"
    using tasks u_rest by simp
  have u_live: "u \<in> rpc_live C"
    by (rule resume_pending_gate_pending_liveD[OF rel u_pending])
  have t_live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  have wf_ctx: "resume_pending_context_wf C"
    using resume_pending_gate_pure_entryD[OF rel]
    by (simp add: resume_pending_entry_rel_def)
  have u_ne_t: "u \<noteq> t"
    using wf_ctx tasks u_rest
    by (auto simp: resume_pending_context_wf_def)
  have q_ne_p: "?q \<noteq> ?p"
  proof
    assume eq: "?q = ?p"
    have geometry: "universal_tcb_geometry (rpc_live C) D"
      using resume_pending_gate_generic_familyD[OF rel]
      by (simp add: scheduler_family_pre_rel_def)
    have disjoint:
      "universal_item_region
         (abi_generic_list_item_ptr (sd_tcb_ptr D u)) \<inter>
       universal_item_region
         (abi_generic_list_item_ptr (sd_tcb_ptr D t)) = {}"
      using universal_different_live_component_regions_disjoint[
        OF geometry u_live t_live u_ne_t,
        where left=GenericItem and right=GenericItem] by simp
    have base:
      "ptr_val (abi_generic_list_item_ptr (sd_tcb_ptr D u)) \<in>
         universal_item_region
           (abi_generic_list_item_ptr (sd_tcb_ptr D u))"
      using intvlI[of 0 20
          "ptr_val (abi_generic_list_item_ptr (sd_tcb_ptr D u))"]
      by (simp add: universal_item_region_size)
    show False
      using base eq disjoint
      by (simp add: resume_pending_generic_raw_ptr_def)
  qed
  have entry_container:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
       (h_val ?h ?q) =
     PTR_COERCE(xLIST_C \<rightarrow> unit) (rpc_generic_owner C u)"
    using resume_pending_gate_tail_owner_entryD[OF rel u_pending]
    by (simp add: scheduler_delay_owner_entry_rel_def)
  have event_step:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
       (h_val (resume_pending_event_remove_heap D t c) ?q) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
       (h_val ?h ?q)"
    using resume_pending_event_remove_generic_item_frame[
      OF rel tasks u_live]
    by simp
  have q_managed: "?q \<in> universal_managed_nodes (rpc_live C) D"
    using u_live
    by (auto simp: resume_pending_generic_raw_ptr_def
        universal_managed_nodes_def)
  have generic_step:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
       (h_val ?hR ?q) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
       (h_val (resume_pending_event_remove_heap D t c) ?q)"
    using resume_pending_generic_remove_family_post[OF rel tasks]
      q_managed q_ne_p
    by (simp add: scheduler_node_kind_family_remove_post_def Let_def
        resume_pending_generic_remove_heap_def)
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
  have insert_bytes:
    "\<forall>a\<in>raw_container_field_region ?q.
       raw_insert_concrete_heap ?hR ?target (?fam ?target) ?p a =
       ?hR a"
    by (rule raw_insert_end_family_container_byte_frame[
      OF pre target fresh p_managed q_managed q_ne_p])
  have heap_inserted:
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
       (resume_pending_ready_inserted_state D C t generic_raw c)) =
     raw_insert_concrete_heap ?hR ?target (?fam ?target) ?p"
    using heap_base
    by (simp add: resume_pending_ready_inserted_heap)
  have insert_step:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
       (h_val (raw_insert_concrete_heap ?hR ?target (?fam ?target) ?p)
         ?q) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
       (h_val ?hR ?q)"
    by (rule raw_container_bytes_to_projection[OF insert_bytes])
  show ?thesis
    using insert_step generic_step event_step entry_container
    by (simp add: heap_inserted)
qed

end
