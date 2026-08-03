theory Scheduler_Resume_Generated_Insert_Owner_Frame
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Body.Scheduler_Resume_Generated_Body"
begin

text \<open>
  The generated insert-end writes the new node's links and container, one
  link field of the cursor and of its successor, and the root's count and
  cursor.  It never writes any node's owner field.  The removal-side member
  owner frame already exists; this theory adds the insertion-side analogue,
  and states it for an arbitrary managed node -- ring members, the inserted
  node itself, and unrelated live items alike -- because re-establishing the
  task observation relation at the drained state needs owner fidelity for
  every live task at once.
\<close>

section \<open>Owner region against link fields of managed nodes\<close>

lemma raw_managed_next_field_owner_disjoint:
  assumes geometry: "universal_tcb_geometry live D"
    and u_managed: "u \<in> universal_managed_nodes live D"
    and w_managed: "w \<in> universal_managed_nodes live D"
  shows
    "raw_pointer_field_region (raw_next_field_ptr u) \<inter>
     raw_owner_field_region w = {}"
proof (cases "u = w")
  case True
  show ?thesis
    using raw_same_item_next_owner_disjoint[where u=w] True by simp
next
  case False
  have items: "raw_item_region u \<inter> raw_item_region w = {}"
    by (rule universal_distinct_managed_item_regions_disjoint[
      OF geometry u_managed w_managed False])
  show ?thesis
    using raw_next_field_region_subset_item[where u=u]
      raw_owner_field_region_subset_item[where p=w] items by blast
qed

lemma raw_managed_prev_field_owner_disjoint:
  assumes geometry: "universal_tcb_geometry live D"
    and u_managed: "u \<in> universal_managed_nodes live D"
    and w_managed: "w \<in> universal_managed_nodes live D"
  shows
    "raw_pointer_field_region (raw_previous_field_ptr u) \<inter>
     raw_owner_field_region w = {}"
proof (cases "u = w")
  case True
  show ?thesis
    using raw_same_item_prev_owner_disjoint[where u=w] True by simp
next
  case False
  have items: "raw_item_region u \<inter> raw_item_region w = {}"
    by (rule universal_distinct_managed_item_regions_disjoint[
      OF geometry u_managed w_managed False])
  show ?thesis
    using raw_previous_field_region_subset_item[where u=u]
      raw_owner_field_region_subset_item[where p=w] items by blast
qed

lemma raw_managed_container_field_owner_disjoint:
  assumes geometry: "universal_tcb_geometry live D"
    and u_managed: "u \<in> universal_managed_nodes live D"
    and w_managed: "w \<in> universal_managed_nodes live D"
  shows
    "raw_container_field_region u \<inter> raw_owner_field_region w = {}"
proof (cases "u = w")
  case True
  show ?thesis
    using raw_same_item_container_owner_disjoint[where u=w] True by simp
next
  case False
  have items: "raw_item_region u \<inter> raw_item_region w = {}"
    by (rule universal_distinct_managed_item_regions_disjoint[
      OF geometry u_managed w_managed False])
  show ?thesis
    using raw_container_field_region_subset_item[where p=u]
      raw_owner_field_region_subset_item[where p=w] items by blast
qed

section \<open>Owner region against link fields of cycle nodes\<close>

lemma raw_family_cycle_next_field_owner_disjoint:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and u_cycle:
      "u \<in> insert (raw_end_item target) (set (ring (fam target)))"
    and w_managed: "w \<in> universal_managed_nodes live D"
  shows
    "raw_pointer_field_region (raw_next_field_ptr u) \<inter>
     raw_owner_field_region w = {}"
proof (cases "u = raw_end_item target")
  case True
  have root_item:
    "raw_list_region target \<inter> raw_item_region w = {}"
    by (rule scheduler_family_root_managed_item_disjoint[
      OF pre target w_managed])
  show ?thesis
    using raw_end_next_field_region_subset_list[where lp=target]
      raw_owner_field_region_subset_item[where p=w] root_item True
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
    by (rule raw_managed_next_field_owner_disjoint[
      OF geometry u_managed w_managed])
qed

lemma raw_family_cycle_prev_field_owner_disjoint:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and u_cycle:
      "u \<in> insert (raw_end_item target) (set (ring (fam target)))"
    and w_managed: "w \<in> universal_managed_nodes live D"
  shows
    "raw_pointer_field_region (raw_previous_field_ptr u) \<inter>
     raw_owner_field_region w = {}"
proof (cases "u = raw_end_item target")
  case True
  have root_item:
    "raw_list_region target \<inter> raw_item_region w = {}"
    by (rule scheduler_family_root_managed_item_disjoint[
      OF pre target w_managed])
  show ?thesis
    using raw_end_previous_field_region_subset_list[where lp=target]
      raw_owner_field_region_subset_item[where p=w] root_item True
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
    by (rule raw_managed_prev_field_owner_disjoint[
      OF geometry u_managed w_managed])
qed

section \<open>Owner bytes of every managed node survive the exact insertion\<close>

theorem raw_insert_end_family_owner_byte_frame:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and fresh: "raw_fresh_for_insert target (ring (fam target)) p"
    and p_managed: "p \<in> universal_managed_nodes live D"
    and w_managed: "w \<in> universal_managed_nodes live D"
  shows
    "\<forall>a\<in>raw_owner_field_region w.
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
     raw_owner_field_region w = {}"
    by (rule raw_managed_next_field_owner_disjoint[
      OF geometry p_managed w_managed])
  have F2:
    "raw_pointer_field_region (raw_previous_field_ptr p) \<inter>
     raw_owner_field_region w = {}"
    by (rule raw_managed_prev_field_owner_disjoint[
      OF geometry p_managed w_managed])
  have F3:
    "raw_pointer_field_region (raw_previous_field_ptr ?q) \<inter>
     raw_owner_field_region w = {}"
    by (rule raw_family_cycle_prev_field_owner_disjoint[
      OF pre target q_cycle w_managed])
  have F4:
    "raw_pointer_field_region (raw_next_field_ptr ?c) \<inter>
     raw_owner_field_region w = {}"
    by (rule raw_family_cycle_next_field_owner_disjoint[
      OF pre target c_cycle w_managed])
  have F5:
    "raw_index_field_region target \<inter> raw_owner_field_region w = {}"
    using raw_index_field_region_subset_list[where lp=target]
      raw_owner_field_region_subset_item[where p=w] root_item by blast
  have F6:
    "raw_container_field_region p \<inter> raw_owner_field_region w = {}"
    by (rule raw_managed_container_field_owner_disjoint[
      OF geometry p_managed w_managed])
  have F7:
    "raw_count_field_region target \<inter> raw_owner_field_region w = {}"
    using raw_count_field_region_subset_list[where lp=target]
      raw_owner_field_region_subset_item[where p=w] root_item by blast
  have outside:
    "\<And>a. a \<in> raw_owner_field_region w \<Longrightarrow>
       a \<notin> raw_insert_end_exact_write_footprint h target (fam target) p"
    unfolding raw_insert_end_exact_write_footprint_def Let_def
    using F1 F2 F3 F4 F5 F6 F7 by blast
  show ?thesis
    using raw_insert_concrete_heap_exact_external_frame[OF rel fresh]
      outside by blast
qed

end
