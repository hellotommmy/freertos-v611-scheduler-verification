theory Scheduler_List_Family_Frame_Capstone
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Ordered_Insert_Generated_Capstone.Scheduler_Ordered_Insert_Generated_Capstone"
    "EAL6_FreeRTOS_V611_List_Insert_End_Generated_Capstone.List_Insert_End_Generated_Capstone"
    "EAL6_FreeRTOS_V611_Scheduler_Remove_Translation_General.Scheduler_Remove_Translation_General"
    "EAL6_FreeRTOS_V611_Scheduler_Universal_Geometry.Scheduler_Universal_Geometry"
begin

text \<open>
  Universal Gate-L storage frame.  There is no enumeration of tasks, roots,
  priorities, ring lengths, cursor cases, endpoint cases, or addresses here.
  A scheduler family may contain any finite set of list roots and any finite
  set of live TCBs.  Sentinel/list and embedded-item aliases internal to their
  C allocations remain permitted.

  raw_family_rel deliberately says nothing about allocations belonging to
  different roots.  scheduler_family_pre_rel adds only the cross-allocation
  facts needed by a family frame: roots do not overlap, root allocations do
  not overlap live TCB allocations, and one embedded item is not owned by two
  roots.  The root-vs-whole-TCB clause is essential: universal_tcb_geometry
  only separates TCBs from one another and cannot rule out an independently
  supplied list-root pointer aliasing a TCB priority field.
  Separation between live embedded items is not assumed; it is derived from
  universal_tcb_geometry, including the adjacent Generic/Event fields of the
  same TCB.
\<close>

definition universal_managed_nodes ::
  "'tid set \<Rightarrow> 'tid scheduler_decode \<Rightarrow> raw_node_id set"
where
  "universal_managed_nodes live D =
     (\<lambda>t. abi_generic_list_item_ptr (sd_tcb_ptr D t)) ` live \<union>
     (\<lambda>t. abi_event_list_item_ptr (sd_tcb_ptr D t)) ` live"

definition raw_xlist_storage ::
  "xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs \<Rightarrow> addr set"
where
  "raw_xlist_storage lp xs =
     raw_list_region lp \<union>
     (\<Union>p\<in>set (ring xs). raw_item_region p)"

definition scheduler_family_pre_rel ::
  "heap_mem \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   'tid set \<Rightarrow> 'tid scheduler_decode \<Rightarrow> bool"
where
  "scheduler_family_pre_rel h roots fam live D \<longleftrightarrow>
     raw_family_rel h roots fam \<and>
     universal_tcb_geometry live D \<and>
     (\<forall>lp\<in>roots.
        set (ring (fam lp)) \<subseteq> universal_managed_nodes live D) \<and>
     (\<forall>lp\<in>roots. \<forall>lq\<in>roots. lp \<noteq> lq \<longrightarrow>
        raw_list_region lp \<inter> raw_list_region lq = {}) \<and>
     (\<forall>lp\<in>roots. \<forall>t\<in>live.
        raw_list_region lp \<inter>
          universal_tcb_region (sd_tcb_ptr D t) = {}) \<and>
     (\<forall>lp\<in>roots. \<forall>lq\<in>roots. lp \<noteq> lq \<longrightarrow>
        set (ring (fam lp)) \<inter> set (ring (fam lq)) = {})"

lemma raw_item_region_eq_universal_item_region:
  "raw_item_region p = universal_item_region p"
  by (simp add: raw_item_region_def universal_item_region_def)

definition raw_owner_field_ptr :: "raw_node_id \<Rightarrow> unit ptr ptr"
where
  "raw_owner_field_ptr p =
     PTR(unit ptr) &(p\<rightarrow>[''pvOwner_C''])"

definition raw_owner_field_region :: "raw_node_id \<Rightarrow> addr set"
where
  "raw_owner_field_region p =
     {ptr_val (raw_owner_field_ptr p)..+size_of TYPE(unit ptr)}"

definition universal_priority_field_ptr ::
  "Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow> 32 word ptr"
where
  "universal_priority_field_ptr tp =
     PTR(32 word) &(tp\<rightarrow>[''uxPriority_C''])"

definition universal_priority_field_region ::
  "Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow> addr set"
where
  "universal_priority_field_region tp =
     {ptr_val (universal_priority_field_ptr tp)..+size_of TYPE(32 word)}"

lemma raw_owner_field_region_subset_item:
  "raw_owner_field_region p \<subseteq> raw_item_region p"
  unfolding raw_owner_field_region_def raw_owner_field_ptr_def
    raw_item_region_def
  apply (simp add: field_lvalue_def xLIST_ITEM_C_pvOwner_C_fl)
  apply (rule intvl_sub_offset)
  by (simp add: size_of_def)

lemma universal_priority_field_region_subset_tcb:
  "universal_priority_field_region tp \<subseteq> universal_tcb_region tp"
  unfolding universal_priority_field_region_def
    universal_priority_field_ptr_def universal_tcb_region_def
  apply (simp add: field_lvalue_def
      Scheduler_V611_Parse.tskTaskControlBlock_C_uxPriority_C_fl)
  apply (rule intvl_sub_offset)
  by (simp add: size_of_def)

lemma universal_same_tcb_generic_event_regions_disjoint:
  "universal_item_region (abi_generic_list_item_ptr tp) \<inter>
   universal_item_region (abi_event_list_item_ptr tp) = {}"
proof -
  have separate:
    "{ptr_val tp + of_nat 4..+20} \<inter>
     {ptr_val tp + of_nat 24..+20} = {}"
    by (subst intvl_disj_offset; rule intvl_disjoint1; simp)
  show ?thesis
    using separate
    by (simp only: universal_item_region_size
        universal_generic_item_ptr_val universal_event_item_ptr_val
        of_nat_numeral)
qed

lemma universal_same_tcb_event_generic_regions_disjoint:
  "universal_item_region (abi_event_list_item_ptr tp) \<inter>
   universal_item_region (abi_generic_list_item_ptr tp) = {}"
  using universal_same_tcb_generic_event_regions_disjoint[where tp=tp]
  by (simp add: Int_commute)

lemma universal_same_tcb_generic_event_ptrs_neq:
  "abi_generic_list_item_ptr tp \<noteq> abi_event_list_item_ptr tp"
proof
  assume equal:
    "abi_generic_list_item_ptr tp = abi_event_list_item_ptr tp"
  have base:
    "ptr_val (abi_generic_list_item_ptr tp) \<in>
       universal_item_region (abi_generic_list_item_ptr tp)"
    using intvlI[of 0 20 "ptr_val (abi_generic_list_item_ptr tp)"]
    by (simp add: universal_item_region_size)
  have common:
    "ptr_val (abi_generic_list_item_ptr tp) \<in>
       universal_item_region (abi_generic_list_item_ptr tp) \<inter>
       universal_item_region (abi_event_list_item_ptr tp)"
    using base equal by simp
  show False
    using common universal_same_tcb_generic_event_regions_disjoint[
      where tp=tp] by simp
qed

lemma universal_same_tcb_generic_priority_regions_disjoint:
  "universal_item_region (abi_generic_list_item_ptr tp) \<inter>
   universal_priority_field_region tp = {}"
proof -
  have separate:
    "{ptr_val tp + of_nat 4..+20} \<inter>
     {ptr_val tp + of_nat 44..+4} = {}"
    by (subst intvl_disj_offset; rule intvl_disjoint1; simp)
  have generic:
    "universal_item_region (abi_generic_list_item_ptr tp) =
     {ptr_val tp + of_nat 4..+20}"
    by (simp only: universal_item_region_size
        universal_generic_item_ptr_val of_nat_numeral)
  have priority:
    "universal_priority_field_region tp =
     {ptr_val tp + of_nat 44..+4}"
    unfolding universal_priority_field_region_def
      universal_priority_field_ptr_def
    by (simp add: field_lvalue_def
        Scheduler_V611_Parse.tskTaskControlBlock_C_uxPriority_C_fl
        size_of_def)
  show ?thesis using separate generic priority by simp
qed

lemma universal_same_tcb_event_priority_regions_disjoint:
  "universal_item_region (abi_event_list_item_ptr tp) \<inter>
   universal_priority_field_region tp = {}"
proof -
  have separate:
    "{ptr_val tp + of_nat 24..+20} \<inter>
     {ptr_val tp + of_nat 44..+4} = {}"
    by (subst intvl_disj_offset; rule intvl_disjoint1; simp)
  have event:
    "universal_item_region (abi_event_list_item_ptr tp) =
     {ptr_val tp + of_nat 24..+20}"
    by (simp only: universal_item_region_size
        universal_event_item_ptr_val of_nat_numeral)
  have priority:
    "universal_priority_field_region tp =
     {ptr_val tp + of_nat 44..+4}"
    unfolding universal_priority_field_region_def
      universal_priority_field_ptr_def
    by (simp add: field_lvalue_def
        Scheduler_V611_Parse.tskTaskControlBlock_C_uxPriority_C_fl
        size_of_def)
  show ?thesis using separate event priority by simp
qed

theorem universal_distinct_managed_item_regions_disjoint:
  assumes geometry: "universal_tcb_geometry live D"
    and p_managed: "p \<in> universal_managed_nodes live D"
    and q_managed: "q \<in> universal_managed_nodes live D"
    and distinct: "p \<noteq> q"
  shows "raw_item_region p \<inter> raw_item_region q = {}"
proof -
  obtain t where t_live: "t \<in> live" and
      p_cases:
        "p = abi_generic_list_item_ptr (sd_tcb_ptr D t) \<or>
         p = abi_event_list_item_ptr (sd_tcb_ptr D t)"
    using p_managed by (auto simp: universal_managed_nodes_def)
  obtain u where u_live: "u \<in> live" and
      q_cases:
        "q = abi_generic_list_item_ptr (sd_tcb_ptr D u) \<or>
         q = abi_event_list_item_ptr (sd_tcb_ptr D u)"
    using q_managed by (auto simp: universal_managed_nodes_def)
  show ?thesis
  proof (cases "t = u")
    case True
    show ?thesis
      using p_cases q_cases distinct True
        universal_same_tcb_generic_event_regions_disjoint[
          where tp="sd_tcb_ptr D t"]
        universal_same_tcb_event_generic_regions_disjoint[
          where tp="sd_tcb_ptr D t"]
      by (auto simp: raw_item_region_eq_universal_item_region)
  next
    case False
    have GG:
      "universal_item_region
          (abi_generic_list_item_ptr (sd_tcb_ptr D t)) \<inter>
       universal_item_region
          (abi_generic_list_item_ptr (sd_tcb_ptr D u)) = {}"
      using universal_different_live_component_regions_disjoint[
        OF geometry t_live u_live False,
        where left=GenericItem and right=GenericItem] by simp
    have GE:
      "universal_item_region
          (abi_generic_list_item_ptr (sd_tcb_ptr D t)) \<inter>
       universal_item_region
          (abi_event_list_item_ptr (sd_tcb_ptr D u)) = {}"
      using universal_different_live_component_regions_disjoint[
        OF geometry t_live u_live False,
        where left=GenericItem and right=EventItem] by simp
    have EG:
      "universal_item_region
          (abi_event_list_item_ptr (sd_tcb_ptr D t)) \<inter>
       universal_item_region
          (abi_generic_list_item_ptr (sd_tcb_ptr D u)) = {}"
      using universal_different_live_component_regions_disjoint[
        OF geometry t_live u_live False,
        where left=EventItem and right=GenericItem] by simp
    have EE:
      "universal_item_region
          (abi_event_list_item_ptr (sd_tcb_ptr D t)) \<inter>
       universal_item_region
          (abi_event_list_item_ptr (sd_tcb_ptr D u)) = {}"
      using universal_different_live_component_regions_disjoint[
        OF geometry t_live u_live False,
        where left=EventItem and right=EventItem] by simp
    show ?thesis
      using p_cases q_cases GG GE EG EE
      by (auto simp: raw_item_region_eq_universal_item_region)
  qed
qed

lemma scheduler_family_root_managed_item_disjoint:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and root: "lp \<in> roots"
    and managed: "p \<in> universal_managed_nodes live D"
  shows "raw_list_region lp \<inter> raw_item_region p = {}"
proof -
  obtain t where t_live: "t \<in> live" and
      p_cases:
        "p = abi_generic_list_item_ptr (sd_tcb_ptr D t) \<or>
         p = abi_event_list_item_ptr (sd_tcb_ptr D t)"
    using managed by (auto simp: universal_managed_nodes_def)
  have root_tcb:
    "raw_list_region lp \<inter>
       universal_tcb_region (sd_tcb_ptr D t) = {}"
    using pre root t_live by (auto simp: scheduler_family_pre_rel_def)
  show ?thesis
    using p_cases root_tcb universal_generic_item_region_subset_tcb[
        where tp="sd_tcb_ptr D t"]
      universal_event_item_region_subset_tcb[
        where tp="sd_tcb_ptr D t"]
    by (auto simp: raw_item_region_eq_universal_item_region)
qed

lemma universal_managed_item_priority_region_disjoint:
  assumes geometry: "universal_tcb_geometry live D"
    and t_live: "t \<in> live"
    and managed: "p \<in> universal_managed_nodes live D"
  shows
    "raw_item_region p \<inter>
     universal_priority_field_region (sd_tcb_ptr D t) = {}"
proof -
  obtain u where u_live: "u \<in> live" and
      p_cases:
        "p = abi_generic_list_item_ptr (sd_tcb_ptr D u) \<or>
         p = abi_event_list_item_ptr (sd_tcb_ptr D u)"
    using managed by (auto simp: universal_managed_nodes_def)
  show ?thesis
  proof (cases "u = t")
    case True
    show ?thesis
      using p_cases True
        universal_same_tcb_generic_priority_regions_disjoint[
          where tp="sd_tcb_ptr D t"]
        universal_same_tcb_event_priority_regions_disjoint[
          where tp="sd_tcb_ptr D t"]
      by (auto simp: raw_item_region_eq_universal_item_region)
  next
    case False
    have generic_tcb:
      "universal_item_region
          (abi_generic_list_item_ptr (sd_tcb_ptr D u)) \<inter>
       universal_tcb_region (sd_tcb_ptr D t) = {}"
      using universal_different_live_component_regions_disjoint[
        OF geometry u_live t_live False,
        where left=GenericItem and right=WholeTCB] by simp
    have event_tcb:
      "universal_item_region
          (abi_event_list_item_ptr (sd_tcb_ptr D u)) \<inter>
       universal_tcb_region (sd_tcb_ptr D t) = {}"
      using universal_different_live_component_regions_disjoint[
        OF geometry u_live t_live False,
        where left=EventItem and right=WholeTCB] by simp
    show ?thesis
      using p_cases generic_tcb event_tcb
        universal_priority_field_region_subset_tcb[
          where tp="sd_tcb_ptr D t"]
      by (auto simp: raw_item_region_eq_universal_item_region)
  qed
qed

theorem scheduler_family_distinct_root_storage_disjoint:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and lp_root: "lp \<in> roots"
    and lq_root: "lq \<in> roots"
    and distinct: "lp \<noteq> lq"
  shows
    "raw_xlist_storage lp (fam lp) \<inter>
     raw_xlist_storage lq (fam lq) = {}"
proof -
  have geometry: "universal_tcb_geometry live D"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have roots:
    "raw_list_region lp \<inter> raw_list_region lq = {}"
    using pre lp_root lq_root distinct
    by (auto simp: scheduler_family_pre_rel_def)
  have lp_managed:
    "set (ring (fam lp)) \<subseteq> universal_managed_nodes live D"
    using pre lp_root by (auto simp: scheduler_family_pre_rel_def)
  have lq_managed:
    "set (ring (fam lq)) \<subseteq> universal_managed_nodes live D"
    using pre lq_root by (auto simp: scheduler_family_pre_rel_def)
  have root_items:
    "\<And>r p. r \<in> roots \<Longrightarrow>
       p \<in> universal_managed_nodes live D \<Longrightarrow>
       raw_list_region r \<inter> raw_item_region p = {}"
    by (rule scheduler_family_root_managed_item_disjoint[OF pre])
  have owners:
    "set (ring (fam lp)) \<inter> set (ring (fam lq)) = {}"
    using pre lp_root lq_root distinct
    by (auto simp: scheduler_family_pre_rel_def)
  have items:
    "\<And>p q. p \<in> set (ring (fam lp)) \<Longrightarrow>
       q \<in> set (ring (fam lq)) \<Longrightarrow>
       raw_item_region p \<inter> raw_item_region q = {}"
  proof -
    fix p q
    assume p: "p \<in> set (ring (fam lp))"
      and q: "q \<in> set (ring (fam lq))"
    have "p \<noteq> q" using owners p q by blast
    then show "raw_item_region p \<inter> raw_item_region q = {}"
      by (rule universal_distinct_managed_item_regions_disjoint[
            OF geometry lp_managed[THEN subsetD, OF p]
              lq_managed[THEN subsetD, OF q]])
  qed
  have root_left_items_right:
    "raw_list_region lp \<inter>
       (\<Union>q\<in>set (ring (fam lq)). raw_item_region q) = {}"
  proof (rule equals0I)
    fix x
    assume member:
      "x \<in> raw_list_region lp \<inter>
        (\<Union>q\<in>set (ring (fam lq)). raw_item_region q)"
    then obtain q where
        q_ring: "q \<in> set (ring (fam lq))"
      and x_root: "x \<in> raw_list_region lp"
      and x_item: "x \<in> raw_item_region q"
      by blast
    have q_managed: "q \<in> universal_managed_nodes live D"
      by (rule subsetD[OF lq_managed q_ring])
    have disjoint:
      "raw_list_region lp \<inter> raw_item_region q = {}"
      by (rule root_items[OF lp_root q_managed])
    show False using disjoint x_root x_item by blast
  qed
  have items_left_root_right:
    "(\<Union>p\<in>set (ring (fam lp)). raw_item_region p) \<inter>
       raw_list_region lq = {}"
  proof (rule equals0I)
    fix x
    assume member:
      "x \<in> (\<Union>p\<in>set (ring (fam lp)). raw_item_region p) \<inter>
        raw_list_region lq"
    then obtain p where
        p_ring: "p \<in> set (ring (fam lp))"
      and x_item: "x \<in> raw_item_region p"
      and x_root: "x \<in> raw_list_region lq"
      by blast
    have p_managed: "p \<in> universal_managed_nodes live D"
      by (rule subsetD[OF lp_managed p_ring])
    have disjoint:
      "raw_list_region lq \<inter> raw_item_region p = {}"
      by (rule root_items[OF lq_root p_managed])
    show False using disjoint x_root x_item by blast
  qed
  have items_left_items_right:
    "(\<Union>p\<in>set (ring (fam lp)). raw_item_region p) \<inter>
     (\<Union>q\<in>set (ring (fam lq)). raw_item_region q) = {}"
  proof (rule equals0I)
    fix x
    assume member:
      "x \<in> (\<Union>p\<in>set (ring (fam lp)). raw_item_region p) \<inter>
       (\<Union>q\<in>set (ring (fam lq)). raw_item_region q)"
    then obtain p q where
        p_ring: "p \<in> set (ring (fam lp))"
      and q_ring: "q \<in> set (ring (fam lq))"
      and x_p: "x \<in> raw_item_region p"
      and x_q: "x \<in> raw_item_region q"
      by blast
    have disjoint: "raw_item_region p \<inter> raw_item_region q = {}"
      by (rule items[OF p_ring q_ring])
    show False using disjoint x_p x_q by blast
  qed
  show ?thesis
    unfolding raw_xlist_storage_def
    using roots root_left_items_right items_left_root_right
      items_left_items_right
    by blast
qed

lemma raw_container_field_region_subset_item:
  "raw_container_field_region p \<subseteq> raw_item_region p"
  unfolding raw_container_field_region_def raw_container_field_ptr_def
    raw_item_region_def
  apply (simp add: field_lvalue_def xLIST_ITEM_C_pvContainer_C_fl)
  apply (rule intvl_sub_offset)
  by (simp add: size_of_def)

lemma raw_cycle_next_field_region_subset_storage:
  assumes cycle:
    "u \<in> insert (raw_end_item lp) (set (ring xs))"
  shows
    "raw_pointer_field_region (raw_next_field_ptr u) \<subseteq>
     raw_xlist_storage lp xs"
proof (cases "u = raw_end_item lp")
  case True
  show ?thesis
    using raw_end_next_field_region_subset_list[where lp=lp] True
    by (auto simp: raw_xlist_storage_def)
next
  case False
  have "u \<in> set (ring xs)" using cycle False by simp
  then show ?thesis
    using raw_next_field_region_subset_item[where u=u]
    by (auto simp: raw_xlist_storage_def)
qed

lemma raw_cycle_previous_field_region_subset_storage:
  assumes cycle:
    "u \<in> insert (raw_end_item lp) (set (ring xs))"
  shows
    "raw_pointer_field_region (raw_previous_field_ptr u) \<subseteq>
     raw_xlist_storage lp xs"
proof (cases "u = raw_end_item lp")
  case True
  show ?thesis
    using raw_end_previous_field_region_subset_list[where lp=lp] True
    by (auto simp: raw_xlist_storage_def)
next
  case False
  have "u \<in> set (ring xs)" using cycle False by simp
  then show ?thesis
    using raw_previous_field_region_subset_item[where u=u]
    by (auto simp: raw_xlist_storage_def)
qed

lemma raw_remove_exact_footprint_subset_storage:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_remove_exact_write_footprint h lp p \<subseteq>
     raw_xlist_storage lp xs"
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
  have p_storage: "raw_item_region p \<subseteq> raw_xlist_storage lp xs"
    using member by (auto simp: raw_xlist_storage_def)
  show ?thesis
    unfolding raw_remove_exact_write_footprint_def
    using raw_cycle_previous_field_region_subset_storage[OF next_cycle]
      raw_cycle_next_field_region_subset_storage[OF previous_cycle]
      raw_index_field_region_subset_list[where lp=lp]
      raw_container_field_region_subset_item[where p=p]
      raw_count_field_region_subset_list[where lp=lp]
      p_storage
    by (auto simp: raw_xlist_storage_def)
qed

lemma raw_ordered_insert_exact_footprint_subset_storage:
  assumes rel: "raw_xlist_rel h lp xs"
  shows
    "raw_ordered_insert_general_exact_write_footprint h lp xs p \<subseteq>
     raw_xlist_storage lp xs \<union> raw_item_region p"
proof -
  let ?before =
    "ordered_scan_prefix (item_key xs) (raw_key_at h p) (ring xs)"
  let ?c = "last (raw_end_item lp # ?before)"
  let ?q = "raw_next_at h lp ?c"
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have c_cycle:
    "?c \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule ordered_scan_predecessor_in_cycle)
  have q_cycle:
    "?q \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_ring_links_next_closed[OF links c_cycle])
  show ?thesis
    unfolding raw_ordered_insert_general_exact_write_footprint_def Let_def
    using raw_next_field_region_subset_item[where u=p]
      raw_previous_field_region_subset_item[where u=p]
      raw_cycle_previous_field_region_subset_storage[OF q_cycle]
      raw_cycle_next_field_region_subset_storage[OF c_cycle]
      raw_container_field_region_subset_item[where p=p]
      raw_count_field_region_subset_list[where lp=lp]
    by (auto simp: raw_xlist_storage_def)
qed

lemma raw_insert_end_exact_footprint_subset_storage:
  assumes rel: "raw_xlist_rel h lp xs"
  shows
    "raw_insert_end_exact_write_footprint h lp xs p \<subseteq>
     raw_xlist_storage lp xs \<union> raw_item_region p"
proof -
  let ?c = "raw_cursor_node lp xs"
  let ?q = "raw_next_at h lp ?c"
  have wf: "xlist_wf xs"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have c_cycle:
    "?c \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_cursor_node_in_cycle[OF wf])
  have q_cycle:
    "?q \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_ring_links_next_closed[OF links c_cycle])
  show ?thesis
    unfolding raw_insert_end_exact_write_footprint_def Let_def
    using raw_next_field_region_subset_item[where u=p]
      raw_previous_field_region_subset_item[where u=p]
      raw_cycle_previous_field_region_subset_storage[OF q_cycle]
      raw_cycle_next_field_region_subset_storage[OF c_cycle]
      raw_index_field_region_subset_list[where lp=lp]
      raw_container_field_region_subset_item[where p=p]
      raw_count_field_region_subset_list[where lp=lp]
    by (auto simp: raw_xlist_storage_def)
qed

lemma scheduler_family_fresh_item_disjoint_non_target_storage:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and other_root: "other \<in> roots"
    and managed: "p \<in> universal_managed_nodes live D"
    and absent: "raw_family_members roots fam p = {}"
  shows
    "raw_item_region p \<inter> raw_xlist_storage other (fam other) = {}"
proof -
  have geometry: "universal_tcb_geometry live D"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have ring_managed:
    "set (ring (fam other)) \<subseteq> universal_managed_nodes live D"
    using pre other_root by (auto simp: scheduler_family_pre_rel_def)
  have root_disjoint:
    "raw_list_region other \<inter> raw_item_region p = {}"
    by (rule scheduler_family_root_managed_item_disjoint[
          OF pre other_root managed])
  have p_absent: "p \<notin> set (ring (fam other))"
    using absent other_root by (auto simp: raw_family_members_def)
  have item_disjoint:
    "\<And>q. q \<in> set (ring (fam other)) \<Longrightarrow>
       raw_item_region p \<inter> raw_item_region q = {}"
  proof -
    fix q
    assume q: "q \<in> set (ring (fam other))"
    have "p \<noteq> q" using p_absent q by blast
    then show "raw_item_region p \<inter> raw_item_region q = {}"
      by (rule universal_distinct_managed_item_regions_disjoint[
            OF geometry managed ring_managed[THEN subsetD, OF q]])
  qed
  show ?thesis
    using root_disjoint item_disjoint
    by (auto simp: raw_xlist_storage_def Int_commute)
qed

lemma scheduler_family_target_storage_disjoint_nonmember_item:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and managed: "p \<in> universal_managed_nodes live D"
    and nonmember: "p \<notin> set (ring (fam target))"
  shows
    "raw_xlist_storage target (fam target) \<inter>
     raw_item_region p = {}"
proof -
  have geometry: "universal_tcb_geometry live D"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have ring_managed:
    "set (ring (fam target)) \<subseteq> universal_managed_nodes live D"
    using pre target by (auto simp: scheduler_family_pre_rel_def)
  have root_disjoint:
    "raw_list_region target \<inter> raw_item_region p = {}"
    by (rule scheduler_family_root_managed_item_disjoint[
          OF pre target managed])
  have item_disjoint:
    "\<And>q. q \<in> set (ring (fam target)) \<Longrightarrow>
       raw_item_region q \<inter> raw_item_region p = {}"
  proof -
    fix q
    assume q: "q \<in> set (ring (fam target))"
    have "q \<noteq> p" using nonmember q by blast
    then show "raw_item_region q \<inter> raw_item_region p = {}"
      by (rule universal_distinct_managed_item_regions_disjoint[
            OF geometry ring_managed[THEN subsetD, OF q] managed])
  qed
  show ?thesis
    using root_disjoint item_disjoint
    by (auto simp: raw_xlist_storage_def)
qed

lemma scheduler_family_target_storage_priority_disjoint:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and t_live: "t \<in> live"
  shows
    "raw_xlist_storage target (fam target) \<inter>
     universal_priority_field_region (sd_tcb_ptr D t) = {}"
proof -
  have geometry: "universal_tcb_geometry live D"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have ring_managed:
    "set (ring (fam target)) \<subseteq> universal_managed_nodes live D"
    using pre target by (auto simp: scheduler_family_pre_rel_def)
  have root_tcb:
    "raw_list_region target \<inter>
       universal_tcb_region (sd_tcb_ptr D t) = {}"
    using pre target t_live by (auto simp: scheduler_family_pre_rel_def)
  have root_priority:
    "raw_list_region target \<inter>
       universal_priority_field_region (sd_tcb_ptr D t) = {}"
    using root_tcb universal_priority_field_region_subset_tcb[
      where tp="sd_tcb_ptr D t"] by blast
  have item_priority:
    "\<And>p. p \<in> set (ring (fam target)) \<Longrightarrow>
       raw_item_region p \<inter>
         universal_priority_field_region (sd_tcb_ptr D t) = {}"
    using universal_managed_item_priority_region_disjoint[
      OF geometry t_live] ring_managed by blast
  show ?thesis
    using root_priority item_priority
    by (auto simp: raw_xlist_storage_def)
qed

theorem raw_remove_family_non_target_byte_frame:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and other: "other \<in> roots"
    and distinct: "target \<noteq> other"
    and member: "p \<in> set (ring (fam target))"
    and address: "a \<in> raw_xlist_storage other (fam other)"
  shows "raw_remove_concrete_heap h p a = h a"
proof -
  have rel: "raw_xlist_rel h target (fam target)"
    using pre target
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have storage_disjoint:
    "raw_xlist_storage target (fam target) \<inter>
       raw_xlist_storage other (fam other) = {}"
    by (rule scheduler_family_distinct_root_storage_disjoint[
          OF pre target other distinct])
  have footprint:
    "raw_remove_exact_write_footprint h target p \<subseteq>
       raw_xlist_storage target (fam target)"
    by (rule raw_remove_exact_footprint_subset_storage[OF rel member])
  have outside: "a \<notin> raw_remove_exact_write_footprint h target p"
    using footprint storage_disjoint address by blast
  show ?thesis
    by (rule raw_remove_concrete_heap_exact_external_frame[
          OF rel member outside])
qed

theorem raw_ordered_insert_family_non_target_byte_frame:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and other: "other \<in> roots"
    and distinct: "target \<noteq> other"
    and fresh: "raw_fresh_for_insert target (ring (fam target)) p"
    and managed: "p \<in> universal_managed_nodes live D"
    and absent: "raw_family_members roots fam p = {}"
    and address: "a \<in> raw_xlist_storage other (fam other)"
  shows "raw_ordered_insert_general_heap h target (fam target) p a = h a"
proof -
  have rel: "raw_xlist_rel h target (fam target)"
    using pre target
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have old_disjoint:
    "raw_xlist_storage target (fam target) \<inter>
       raw_xlist_storage other (fam other) = {}"
    by (rule scheduler_family_distinct_root_storage_disjoint[
          OF pre target other distinct])
  have p_disjoint:
    "raw_item_region p \<inter> raw_xlist_storage other (fam other) = {}"
    by (rule scheduler_family_fresh_item_disjoint_non_target_storage[
          OF pre other managed absent])
  have footprint:
    "raw_ordered_insert_general_exact_write_footprint
       h target (fam target) p \<subseteq>
       raw_xlist_storage target (fam target) \<union> raw_item_region p"
    by (rule raw_ordered_insert_exact_footprint_subset_storage[OF rel])
  have outside:
    "a \<notin> raw_ordered_insert_general_exact_write_footprint
       h target (fam target) p"
    using footprint old_disjoint p_disjoint address by blast
  show ?thesis
    by (rule raw_ordered_insert_general_heap_exact_external_frame[
          OF rel fresh outside])
qed

theorem raw_insert_end_family_non_target_byte_frame:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and other: "other \<in> roots"
    and distinct: "target \<noteq> other"
    and fresh: "raw_fresh_for_insert target (ring (fam target)) p"
    and managed: "p \<in> universal_managed_nodes live D"
    and absent: "raw_family_members roots fam p = {}"
    and address: "a \<in> raw_xlist_storage other (fam other)"
  shows "raw_insert_concrete_heap h target (fam target) p a = h a"
proof -
  have rel: "raw_xlist_rel h target (fam target)"
    using pre target
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have old_disjoint:
    "raw_xlist_storage target (fam target) \<inter>
       raw_xlist_storage other (fam other) = {}"
    by (rule scheduler_family_distinct_root_storage_disjoint[
          OF pre target other distinct])
  have p_disjoint:
    "raw_item_region p \<inter> raw_xlist_storage other (fam other) = {}"
    by (rule scheduler_family_fresh_item_disjoint_non_target_storage[
          OF pre other managed absent])
  have footprint:
    "raw_insert_end_exact_write_footprint h target (fam target) p \<subseteq>
       raw_xlist_storage target (fam target) \<union> raw_item_region p"
    by (rule raw_insert_end_exact_footprint_subset_storage[OF rel])
  have outside:
    "a \<notin> raw_insert_end_exact_write_footprint
       h target (fam target) p"
    using footprint old_disjoint p_disjoint address by blast
  show ?thesis
    by (rule raw_insert_concrete_heap_exact_external_frame[
          OF rel fresh outside])
qed

theorem raw_remove_family_sibling_item_priority_byte_frame:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and member: "p \<in> set (ring (fam target))"
    and sibling_managed:
      "sibling \<in> universal_managed_nodes live D"
    and sibling_nonmember:
      "sibling \<notin> set (ring (fam target))"
    and t_live: "t \<in> live"
  shows
    "(\<forall>a\<in>raw_item_region sibling.
       raw_remove_concrete_heap h p a = h a) \<and>
     (\<forall>a\<in>universal_priority_field_region (sd_tcb_ptr D t).
       raw_remove_concrete_heap h p a = h a)"
proof -
  have rel: "raw_xlist_rel h target (fam target)"
    using pre target
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have footprint:
    "raw_remove_exact_write_footprint h target p \<subseteq>
       raw_xlist_storage target (fam target)"
    by (rule raw_remove_exact_footprint_subset_storage[OF rel member])
  have sibling_storage:
    "raw_xlist_storage target (fam target) \<inter>
       raw_item_region sibling = {}"
    by (rule scheduler_family_target_storage_disjoint_nonmember_item[
          OF pre target sibling_managed sibling_nonmember])
  have item_outside:
    "\<And>a. a \<in> raw_item_region sibling \<Longrightarrow>
       a \<notin> raw_remove_exact_write_footprint h target p"
    using footprint sibling_storage by blast
  have priority_storage:
    "raw_xlist_storage target (fam target) \<inter>
       universal_priority_field_region (sd_tcb_ptr D t) = {}"
    by (rule scheduler_family_target_storage_priority_disjoint[
          OF pre target t_live])
  have priority_outside:
    "\<And>a. a \<in> universal_priority_field_region (sd_tcb_ptr D t)
       \<Longrightarrow> a \<notin> raw_remove_exact_write_footprint h target p"
    using footprint priority_storage by blast
  show ?thesis
    using raw_remove_concrete_heap_exact_external_frame[
      OF rel member] item_outside priority_outside by blast
qed

theorem raw_remove_family_sibling_owner_priority_byte_frame:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and member: "p \<in> set (ring (fam target))"
    and sibling_managed:
      "sibling \<in> universal_managed_nodes live D"
    and sibling_nonmember:
      "sibling \<notin> set (ring (fam target))"
    and t_live: "t \<in> live"
  shows
    "(\<forall>a\<in>raw_owner_field_region sibling.
       raw_remove_concrete_heap h p a = h a) \<and>
     (\<forall>a\<in>universal_priority_field_region (sd_tcb_ptr D t).
       raw_remove_concrete_heap h p a = h a)"
proof -
  have rel: "raw_xlist_rel h target (fam target)"
    using pre target
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have footprint:
    "raw_remove_exact_write_footprint h target p \<subseteq>
       raw_xlist_storage target (fam target)"
    by (rule raw_remove_exact_footprint_subset_storage[OF rel member])
  have sibling_storage:
    "raw_xlist_storage target (fam target) \<inter>
       raw_item_region sibling = {}"
    by (rule scheduler_family_target_storage_disjoint_nonmember_item[
          OF pre target sibling_managed sibling_nonmember])
  have owner_outside:
    "\<And>a. a \<in> raw_owner_field_region sibling \<Longrightarrow>
       a \<notin> raw_remove_exact_write_footprint h target p"
    using footprint sibling_storage raw_owner_field_region_subset_item[
      where p=sibling] by blast
  have priority_storage:
    "raw_xlist_storage target (fam target) \<inter>
       universal_priority_field_region (sd_tcb_ptr D t) = {}"
    by (rule scheduler_family_target_storage_priority_disjoint[
          OF pre target t_live])
  have priority_outside:
    "\<And>a. a \<in> universal_priority_field_region (sd_tcb_ptr D t)
       \<Longrightarrow> a \<notin> raw_remove_exact_write_footprint h target p"
    using footprint priority_storage by blast
  show ?thesis
    using raw_remove_concrete_heap_exact_external_frame[
      OF rel member] owner_outside priority_outside by blast
qed

theorem raw_ordered_insert_family_sibling_item_priority_byte_frame:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and fresh: "raw_fresh_for_insert target (ring (fam target)) p"
    and p_managed: "p \<in> universal_managed_nodes live D"
    and sibling_managed:
      "sibling \<in> universal_managed_nodes live D"
    and p_sibling: "p \<noteq> sibling"
    and sibling_nonmember:
      "sibling \<notin> set (ring (fam target))"
    and t_live: "t \<in> live"
  shows
    "(\<forall>a\<in>raw_item_region sibling.
       raw_ordered_insert_general_heap h target (fam target) p a = h a) \<and>
     (\<forall>a\<in>universal_priority_field_region (sd_tcb_ptr D t).
       raw_ordered_insert_general_heap h target (fam target) p a = h a)"
proof -
  have geometry: "universal_tcb_geometry live D"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have rel: "raw_xlist_rel h target (fam target)"
    using pre target
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have footprint:
    "raw_ordered_insert_general_exact_write_footprint
       h target (fam target) p \<subseteq>
       raw_xlist_storage target (fam target) \<union> raw_item_region p"
    by (rule raw_ordered_insert_exact_footprint_subset_storage[OF rel])
  have sibling_storage:
    "raw_xlist_storage target (fam target) \<inter>
       raw_item_region sibling = {}"
    by (rule scheduler_family_target_storage_disjoint_nonmember_item[
          OF pre target sibling_managed sibling_nonmember])
  have p_sibling_regions:
    "raw_item_region p \<inter> raw_item_region sibling = {}"
    by (rule universal_distinct_managed_item_regions_disjoint[
          OF geometry p_managed sibling_managed p_sibling])
  have item_outside:
    "\<And>a. a \<in> raw_item_region sibling \<Longrightarrow>
       a \<notin> raw_ordered_insert_general_exact_write_footprint
         h target (fam target) p"
    using footprint sibling_storage p_sibling_regions by blast
  have storage_priority:
    "raw_xlist_storage target (fam target) \<inter>
       universal_priority_field_region (sd_tcb_ptr D t) = {}"
    by (rule scheduler_family_target_storage_priority_disjoint[
          OF pre target t_live])
  have p_priority:
    "raw_item_region p \<inter>
       universal_priority_field_region (sd_tcb_ptr D t) = {}"
    by (rule universal_managed_item_priority_region_disjoint[
          OF geometry t_live p_managed])
  have priority_outside:
    "\<And>a. a \<in> universal_priority_field_region (sd_tcb_ptr D t)
       \<Longrightarrow>
       a \<notin> raw_ordered_insert_general_exact_write_footprint
         h target (fam target) p"
    using footprint storage_priority p_priority by blast
  show ?thesis
    using raw_ordered_insert_general_heap_exact_external_frame[
      OF rel fresh] item_outside priority_outside by blast
qed

theorem raw_ordered_insert_family_sibling_owner_priority_byte_frame:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and fresh: "raw_fresh_for_insert target (ring (fam target)) p"
    and p_managed: "p \<in> universal_managed_nodes live D"
    and sibling_managed:
      "sibling \<in> universal_managed_nodes live D"
    and p_sibling: "p \<noteq> sibling"
    and sibling_nonmember:
      "sibling \<notin> set (ring (fam target))"
    and t_live: "t \<in> live"
  shows
    "(\<forall>a\<in>raw_owner_field_region sibling.
       raw_ordered_insert_general_heap h target (fam target) p a = h a) \<and>
     (\<forall>a\<in>universal_priority_field_region (sd_tcb_ptr D t).
       raw_ordered_insert_general_heap h target (fam target) p a = h a)"
proof -
  have geometry: "universal_tcb_geometry live D"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have rel: "raw_xlist_rel h target (fam target)"
    using pre target
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have footprint:
    "raw_ordered_insert_general_exact_write_footprint
       h target (fam target) p \<subseteq>
       raw_xlist_storage target (fam target) \<union> raw_item_region p"
    by (rule raw_ordered_insert_exact_footprint_subset_storage[OF rel])
  have sibling_storage:
    "raw_xlist_storage target (fam target) \<inter>
       raw_item_region sibling = {}"
    by (rule scheduler_family_target_storage_disjoint_nonmember_item[
          OF pre target sibling_managed sibling_nonmember])
  have p_sibling_regions:
    "raw_item_region p \<inter> raw_item_region sibling = {}"
    by (rule universal_distinct_managed_item_regions_disjoint[
          OF geometry p_managed sibling_managed p_sibling])
  have owner_outside:
    "\<And>a. a \<in> raw_owner_field_region sibling \<Longrightarrow>
       a \<notin> raw_ordered_insert_general_exact_write_footprint
         h target (fam target) p"
    using footprint sibling_storage p_sibling_regions
      raw_owner_field_region_subset_item[where p=sibling] by blast
  have storage_priority:
    "raw_xlist_storage target (fam target) \<inter>
       universal_priority_field_region (sd_tcb_ptr D t) = {}"
    by (rule scheduler_family_target_storage_priority_disjoint[
          OF pre target t_live])
  have p_priority:
    "raw_item_region p \<inter>
       universal_priority_field_region (sd_tcb_ptr D t) = {}"
    by (rule universal_managed_item_priority_region_disjoint[
          OF geometry t_live p_managed])
  have priority_outside:
    "\<And>a. a \<in> universal_priority_field_region (sd_tcb_ptr D t)
       \<Longrightarrow>
       a \<notin> raw_ordered_insert_general_exact_write_footprint
         h target (fam target) p"
    using footprint storage_priority p_priority by blast
  show ?thesis
    using raw_ordered_insert_general_heap_exact_external_frame[
      OF rel fresh] owner_outside priority_outside by blast
qed

theorem raw_insert_end_family_sibling_item_priority_byte_frame:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and fresh: "raw_fresh_for_insert target (ring (fam target)) p"
    and p_managed: "p \<in> universal_managed_nodes live D"
    and sibling_managed:
      "sibling \<in> universal_managed_nodes live D"
    and p_sibling: "p \<noteq> sibling"
    and sibling_nonmember:
      "sibling \<notin> set (ring (fam target))"
    and t_live: "t \<in> live"
  shows
    "(\<forall>a\<in>raw_item_region sibling.
       raw_insert_concrete_heap h target (fam target) p a = h a) \<and>
     (\<forall>a\<in>universal_priority_field_region (sd_tcb_ptr D t).
       raw_insert_concrete_heap h target (fam target) p a = h a)"
proof -
  have geometry: "universal_tcb_geometry live D"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have rel: "raw_xlist_rel h target (fam target)"
    using pre target
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have footprint:
    "raw_insert_end_exact_write_footprint h target (fam target) p \<subseteq>
       raw_xlist_storage target (fam target) \<union> raw_item_region p"
    by (rule raw_insert_end_exact_footprint_subset_storage[OF rel])
  have sibling_storage:
    "raw_xlist_storage target (fam target) \<inter>
       raw_item_region sibling = {}"
    by (rule scheduler_family_target_storage_disjoint_nonmember_item[
          OF pre target sibling_managed sibling_nonmember])
  have p_sibling_regions:
    "raw_item_region p \<inter> raw_item_region sibling = {}"
    by (rule universal_distinct_managed_item_regions_disjoint[
          OF geometry p_managed sibling_managed p_sibling])
  have item_outside:
    "\<And>a. a \<in> raw_item_region sibling \<Longrightarrow>
       a \<notin> raw_insert_end_exact_write_footprint
         h target (fam target) p"
    using footprint sibling_storage p_sibling_regions by blast
  have storage_priority:
    "raw_xlist_storage target (fam target) \<inter>
       universal_priority_field_region (sd_tcb_ptr D t) = {}"
    by (rule scheduler_family_target_storage_priority_disjoint[
          OF pre target t_live])
  have p_priority:
    "raw_item_region p \<inter>
       universal_priority_field_region (sd_tcb_ptr D t) = {}"
    by (rule universal_managed_item_priority_region_disjoint[
          OF geometry t_live p_managed])
  have priority_outside:
    "\<And>a. a \<in> universal_priority_field_region (sd_tcb_ptr D t)
       \<Longrightarrow>
       a \<notin> raw_insert_end_exact_write_footprint
         h target (fam target) p"
    using footprint storage_priority p_priority by blast
  show ?thesis
    using raw_insert_concrete_heap_exact_external_frame[
      OF rel fresh] item_outside priority_outside by blast
qed

theorem raw_insert_end_family_sibling_owner_priority_byte_frame:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and fresh: "raw_fresh_for_insert target (ring (fam target)) p"
    and p_managed: "p \<in> universal_managed_nodes live D"
    and sibling_managed:
      "sibling \<in> universal_managed_nodes live D"
    and p_sibling: "p \<noteq> sibling"
    and sibling_nonmember:
      "sibling \<notin> set (ring (fam target))"
    and t_live: "t \<in> live"
  shows
    "(\<forall>a\<in>raw_owner_field_region sibling.
       raw_insert_concrete_heap h target (fam target) p a = h a) \<and>
     (\<forall>a\<in>universal_priority_field_region (sd_tcb_ptr D t).
       raw_insert_concrete_heap h target (fam target) p a = h a)"
proof -
  have geometry: "universal_tcb_geometry live D"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have rel: "raw_xlist_rel h target (fam target)"
    using pre target
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have footprint:
    "raw_insert_end_exact_write_footprint h target (fam target) p \<subseteq>
       raw_xlist_storage target (fam target) \<union> raw_item_region p"
    by (rule raw_insert_end_exact_footprint_subset_storage[OF rel])
  have sibling_storage:
    "raw_xlist_storage target (fam target) \<inter>
       raw_item_region sibling = {}"
    by (rule scheduler_family_target_storage_disjoint_nonmember_item[
          OF pre target sibling_managed sibling_nonmember])
  have p_sibling_regions:
    "raw_item_region p \<inter> raw_item_region sibling = {}"
    by (rule universal_distinct_managed_item_regions_disjoint[
          OF geometry p_managed sibling_managed p_sibling])
  have owner_outside:
    "\<And>a. a \<in> raw_owner_field_region sibling \<Longrightarrow>
       a \<notin> raw_insert_end_exact_write_footprint
         h target (fam target) p"
    using footprint sibling_storage p_sibling_regions
      raw_owner_field_region_subset_item[where p=sibling] by blast
  have storage_priority:
    "raw_xlist_storage target (fam target) \<inter>
       universal_priority_field_region (sd_tcb_ptr D t) = {}"
    by (rule scheduler_family_target_storage_priority_disjoint[
          OF pre target t_live])
  have p_priority:
    "raw_item_region p \<inter>
       universal_priority_field_region (sd_tcb_ptr D t) = {}"
    by (rule universal_managed_item_priority_region_disjoint[
          OF geometry t_live p_managed])
  have priority_outside:
    "\<And>a. a \<in> universal_priority_field_region (sd_tcb_ptr D t)
       \<Longrightarrow>
       a \<notin> raw_insert_end_exact_write_footprint
         h target (fam target) p"
    using footprint storage_priority p_priority by blast
  show ?thesis
    using raw_insert_concrete_heap_exact_external_frame[
      OF rel fresh] owner_outside priority_outside by blast
qed

theorem scheduler_family_three_list_primitives_non_target_capstone:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and other: "other \<in> roots"
    and distinct: "target \<noteq> other"
    and remove_member: "p_remove \<in> set (ring (fam target))"
    and ordered_fresh:
      "raw_fresh_for_insert target (ring (fam target)) p_ordered"
    and end_fresh:
      "raw_fresh_for_insert target (ring (fam target)) p_end"
    and ordered_managed:
      "p_ordered \<in> universal_managed_nodes live D"
    and end_managed:
      "p_end \<in> universal_managed_nodes live D"
    and ordered_absent:
      "raw_family_members roots fam p_ordered = {}"
    and end_absent:
      "raw_family_members roots fam p_end = {}"
    and address: "a \<in> raw_xlist_storage other (fam other)"
  shows
    "raw_remove_concrete_heap h p_remove a = h a \<and>
     raw_ordered_insert_general_heap
       h target (fam target) p_ordered a = h a \<and>
     raw_insert_concrete_heap h target (fam target) p_end a = h a"
  using raw_remove_family_non_target_byte_frame[
      OF pre target other distinct remove_member address]
    raw_ordered_insert_family_non_target_byte_frame[
      OF pre target other distinct ordered_fresh ordered_managed
        ordered_absent address]
    raw_insert_end_family_non_target_byte_frame[
      OF pre target other distinct end_fresh end_managed end_absent address]
  by blast

end
