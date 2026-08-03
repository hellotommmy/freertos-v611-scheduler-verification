theory Scheduler_Resume_Generated_Insert_Key_Frame
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Drained_Relabel.Scheduler_Resume_Generated_Drained_Relabel"
begin

text \<open>
  The drained gate relation's key clause records every live task's wake key
  directly in the heap.  The removal preservation already keeps every
  managed key; this theory adds the insertion-side analogue at the item
  value field, mirroring the owner frame: the exact insert-end footprint
  misses every managed node's key field, so all wake keys survive the drain
  body's final write.
\<close>

section \<open>Key field regions\<close>

definition raw_key_field_ptr :: "raw_node_id \<Rightarrow> 32 word ptr"
where
  "raw_key_field_ptr p =
     PTR(32 word) &(p\<rightarrow>[''xItemValue_C''])"

definition raw_key_field_region :: "raw_node_id \<Rightarrow> addr set"
where
  "raw_key_field_region p =
     {ptr_val (raw_key_field_ptr p)..+size_of TYPE(32 word)}"

lemma raw_key_field_region_subset_item:
  "raw_key_field_region p \<subseteq> raw_item_region p"
  unfolding raw_key_field_region_def raw_key_field_ptr_def
    raw_item_region_def
  apply (simp add: field_lvalue_def xLIST_ITEM_C_xItemValue_C_fl)
  apply (rule intvl_start_le)
  by (simp add: size_of_def)

lemma raw_key_bytes_to_projection:
  assumes bytes: "\<forall>a\<in>raw_key_field_region q. h' a = h a"
  shows "raw_key_at h' q = raw_key_at h q"
proof -
  have field_same:
    "h_val h' (raw_key_field_ptr q) = h_val h (raw_key_field_ptr q)"
  proof (rule delay_h_val_region_cong)
    fix address
    assume "address \<in>
      {ptr_val (raw_key_field_ptr q)..+size_of TYPE(32 word)}"
    then show "h' address = h address"
      using bytes by (simp add: raw_key_field_region_def)
  qed
  show ?thesis
    using field_same
    unfolding raw_key_field_ptr_def raw_key_at_def
    by (simp only:
      List_V611_Raw_Skip_Translation.xLIST_ITEM_C_h_val_fields(1))
qed

section \<open>Intra-item field disjointness for the key field\<close>

lemma raw_same_item_next_key_disjoint:
  "raw_pointer_field_region (raw_next_field_ptr u) \<inter>
   raw_key_field_region u = {}"
proof -
  have separate:
    "{ptr_val u + of_nat 0..+4} \<inter> {ptr_val u + of_nat 4..+4} = {}"
    by (subst intvl_disj_offset; rule intvl_disjoint1; simp)
  show ?thesis
    using separate
    unfolding raw_pointer_field_region_def raw_next_field_ptr_def
      raw_key_field_region_def raw_key_field_ptr_def
    by (auto simp: field_lvalue_def xLIST_ITEM_C_pxNext_C_fl
        xLIST_ITEM_C_xItemValue_C_fl size_of_def)
qed

lemma raw_same_item_prev_key_disjoint:
  "raw_pointer_field_region (raw_previous_field_ptr u) \<inter>
   raw_key_field_region u = {}"
proof -
  have separate:
    "{ptr_val u + of_nat 0..+4} \<inter> {ptr_val u + of_nat 8..+4} = {}"
    by (subst intvl_disj_offset; rule intvl_disjoint1; simp)
  show ?thesis
    using separate
    unfolding raw_pointer_field_region_def raw_previous_field_ptr_def
      raw_key_field_region_def raw_key_field_ptr_def
    by (auto simp: field_lvalue_def xLIST_ITEM_C_pxPrevious_C_fl
        xLIST_ITEM_C_xItemValue_C_fl size_of_def)
qed

lemma raw_same_item_container_key_disjoint:
  "raw_container_field_region u \<inter> raw_key_field_region u = {}"
proof -
  have separate:
    "{ptr_val u + of_nat 0..+4} \<inter> {ptr_val u + of_nat 16..+4} = {}"
    by (subst intvl_disj_offset; rule intvl_disjoint1; simp)
  show ?thesis
    using separate
    unfolding raw_container_field_region_def raw_container_field_ptr_def
      raw_key_field_region_def raw_key_field_ptr_def
    by (auto simp: field_lvalue_def xLIST_ITEM_C_pvContainer_C_fl
        xLIST_ITEM_C_xItemValue_C_fl size_of_def)
qed

section \<open>Key region against link fields of managed and cycle nodes\<close>

lemma raw_managed_next_field_key_disjoint:
  assumes geometry: "universal_tcb_geometry live D"
    and u_managed: "u \<in> universal_managed_nodes live D"
    and w_managed: "w \<in> universal_managed_nodes live D"
  shows
    "raw_pointer_field_region (raw_next_field_ptr u) \<inter>
     raw_key_field_region w = {}"
proof (cases "u = w")
  case True
  show ?thesis
    using raw_same_item_next_key_disjoint[where u=w] True by simp
next
  case False
  have items: "raw_item_region u \<inter> raw_item_region w = {}"
    by (rule universal_distinct_managed_item_regions_disjoint[
      OF geometry u_managed w_managed False])
  show ?thesis
    using raw_next_field_region_subset_item[where u=u]
      raw_key_field_region_subset_item[where p=w] items by blast
qed

lemma raw_managed_prev_field_key_disjoint:
  assumes geometry: "universal_tcb_geometry live D"
    and u_managed: "u \<in> universal_managed_nodes live D"
    and w_managed: "w \<in> universal_managed_nodes live D"
  shows
    "raw_pointer_field_region (raw_previous_field_ptr u) \<inter>
     raw_key_field_region w = {}"
proof (cases "u = w")
  case True
  show ?thesis
    using raw_same_item_prev_key_disjoint[where u=w] True by simp
next
  case False
  have items: "raw_item_region u \<inter> raw_item_region w = {}"
    by (rule universal_distinct_managed_item_regions_disjoint[
      OF geometry u_managed w_managed False])
  show ?thesis
    using raw_previous_field_region_subset_item[where u=u]
      raw_key_field_region_subset_item[where p=w] items by blast
qed

lemma raw_managed_container_field_key_disjoint:
  assumes geometry: "universal_tcb_geometry live D"
    and u_managed: "u \<in> universal_managed_nodes live D"
    and w_managed: "w \<in> universal_managed_nodes live D"
  shows
    "raw_container_field_region u \<inter> raw_key_field_region w = {}"
proof (cases "u = w")
  case True
  show ?thesis
    using raw_same_item_container_key_disjoint[where u=w] True by simp
next
  case False
  have items: "raw_item_region u \<inter> raw_item_region w = {}"
    by (rule universal_distinct_managed_item_regions_disjoint[
      OF geometry u_managed w_managed False])
  show ?thesis
    using raw_container_field_region_subset_item[where p=u]
      raw_key_field_region_subset_item[where p=w] items by blast
qed

lemma raw_family_cycle_next_field_key_disjoint:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and u_cycle:
      "u \<in> insert (raw_end_item target) (set (ring (fam target)))"
    and w_managed: "w \<in> universal_managed_nodes live D"
  shows
    "raw_pointer_field_region (raw_next_field_ptr u) \<inter>
     raw_key_field_region w = {}"
proof (cases "u = raw_end_item target")
  case True
  have root_item:
    "raw_list_region target \<inter> raw_item_region w = {}"
    by (rule scheduler_family_root_managed_item_disjoint[
      OF pre target w_managed])
  show ?thesis
    using raw_end_next_field_region_subset_list[where lp=target]
      raw_key_field_region_subset_item[where p=w] root_item True
    by blast
next
  case False
  have geometry: "universal_tcb_geometry live D"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have ring_managed:
    "set (ring (fam target)) \<subseteq> universal_managed_nodes live D"
    using pre target by (auto simp: scheduler_family_pre_rel_def)
  have u_managed: "u \<in> universal_managed_nodes live D"
    using u_cycle False ring_managed by auto
  show ?thesis
    by (rule raw_managed_next_field_key_disjoint[
      OF geometry u_managed w_managed])
qed

lemma raw_family_cycle_prev_field_key_disjoint:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and u_cycle:
      "u \<in> insert (raw_end_item target) (set (ring (fam target)))"
    and w_managed: "w \<in> universal_managed_nodes live D"
  shows
    "raw_pointer_field_region (raw_previous_field_ptr u) \<inter>
     raw_key_field_region w = {}"
proof (cases "u = raw_end_item target")
  case True
  have root_item:
    "raw_list_region target \<inter> raw_item_region w = {}"
    by (rule scheduler_family_root_managed_item_disjoint[
      OF pre target w_managed])
  show ?thesis
    using raw_end_previous_field_region_subset_list[where lp=target]
      raw_key_field_region_subset_item[where p=w] root_item True
    by blast
next
  case False
  have geometry: "universal_tcb_geometry live D"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have ring_managed:
    "set (ring (fam target)) \<subseteq> universal_managed_nodes live D"
    using pre target by (auto simp: scheduler_family_pre_rel_def)
  have u_managed: "u \<in> universal_managed_nodes live D"
    using u_cycle False ring_managed by auto
  show ?thesis
    by (rule raw_managed_prev_field_key_disjoint[
      OF geometry u_managed w_managed])
qed

section \<open>Key bytes of every managed node survive the exact insertion\<close>

theorem raw_insert_end_family_key_byte_frame:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and fresh: "raw_fresh_for_insert target (ring (fam target)) p"
    and p_managed: "p \<in> universal_managed_nodes live D"
    and w_managed: "w \<in> universal_managed_nodes live D"
  shows
    "\<forall>a\<in>raw_key_field_region w.
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
     raw_key_field_region w = {}"
    by (rule raw_managed_next_field_key_disjoint[
      OF geometry p_managed w_managed])
  have F2:
    "raw_pointer_field_region (raw_previous_field_ptr p) \<inter>
     raw_key_field_region w = {}"
    by (rule raw_managed_prev_field_key_disjoint[
      OF geometry p_managed w_managed])
  have F3:
    "raw_pointer_field_region (raw_previous_field_ptr ?q) \<inter>
     raw_key_field_region w = {}"
    by (rule raw_family_cycle_prev_field_key_disjoint[
      OF pre target q_cycle w_managed])
  have F4:
    "raw_pointer_field_region (raw_next_field_ptr ?c) \<inter>
     raw_key_field_region w = {}"
    by (rule raw_family_cycle_next_field_key_disjoint[
      OF pre target c_cycle w_managed])
  have F5:
    "raw_index_field_region target \<inter> raw_key_field_region w = {}"
    using raw_index_field_region_subset_list[where lp=target]
      raw_key_field_region_subset_item[where p=w] root_item by blast
  have F6:
    "raw_container_field_region p \<inter> raw_key_field_region w = {}"
    by (rule raw_managed_container_field_key_disjoint[
      OF geometry p_managed w_managed])
  have F7:
    "raw_count_field_region target \<inter> raw_key_field_region w = {}"
    using raw_count_field_region_subset_list[where lp=target]
      raw_key_field_region_subset_item[where p=w] root_item by blast
  have outside:
    "\<And>a. a \<in> raw_key_field_region w \<Longrightarrow>
       a \<notin> raw_insert_end_exact_write_footprint h target (fam target) p"
    unfolding raw_insert_end_exact_write_footprint_def Let_def
    using F1 F2 F3 F4 F5 F6 F7 by blast
  show ?thesis
    using raw_insert_concrete_heap_exact_external_frame[OF rel fresh]
      outside by blast
qed

section \<open>Every live wake key survives to the drained state\<close>

theorem resume_pending_drained_keys:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and live: "u \<in> rpc_live C"
  shows
    "raw_key_at
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
       (resume_pending_generic_raw_ptr D u) = rpc_K_G C u"
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
    "\<forall>a\<in>raw_key_field_region ?q.
       raw_insert_concrete_heap ?hR ?target (?fam ?target) ?p a = ?hR a"
    by (rule raw_insert_end_family_key_byte_frame[
      OF pre target fresh p_managed q_managed])
  have heap_inserted:
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
       (resume_pending_ready_inserted_state D C t generic_raw c)) =
     raw_insert_concrete_heap ?hR ?target (?fam ?target) ?p"
    using heap_base
    by (simp add: resume_pending_ready_inserted_heap)
  have removal_key: "raw_key_at ?hR ?q = rpc_K_G C u"
    using resume_pending_generic_remove_family_post[OF rel tasks] live
    by blast
  have insert_key:
    "raw_key_at
       (raw_insert_concrete_heap ?hR ?target (?fam ?target) ?p) ?q =
     raw_key_at ?hR ?q"
    by (rule raw_key_bytes_to_projection[OF bytes])
  show ?thesis
    using insert_key removal_key by (simp add: heap_inserted)
qed

end
