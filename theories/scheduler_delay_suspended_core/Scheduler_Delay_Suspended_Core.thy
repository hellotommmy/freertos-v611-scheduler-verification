theory Scheduler_Delay_Suspended_Core
  imports
    "EAL6_FreeRTOS_V611_Scheduler_List_Family_Frame_Capstone.Scheduler_List_Family_Frame_Capstone"
    "EAL6_FreeRTOS_V611_Scheduler_Delay_Endpoint_Bridge.Scheduler_Delay_Endpoint_Bridge"
begin

text \<open>
  Gate-H suspended-core composition.  Every task identity, priority, tick,
  positive delay, list root, ring, cursor, endpoint and alias configuration is
  quantified.  The current/overflow delayed root is computed from the source
  word comparison; it is never supplied as a selected-root premise.

  The first layer below turns the byte frames already proved for the generated
  list primitives into preservation of an arbitrary raw list relation.  This
  is the missing bridge needed to compose remove, wake-key write and ordered
  insert without assuming a post-shaped list relation.
\<close>

lemma delay_h_val_region_cong:
  fixes p :: "'a::mem_type ptr"
  assumes frame: "\<And>a. a \<in> {ptr_val p..+size_of TYPE('a)} \<Longrightarrow>
      h' a = h a"
  shows "h_val h' p = h_val h p"
proof -
  have lists:
    "heap_list h' (size_of TYPE('a)) (ptr_val p) =
     heap_list h (size_of TYPE('a)) (ptr_val p)"
    by (rule heap_list_h_eq2; rule frame)
  show ?thesis using lists by (simp add: h_val_def)
qed

lemma delay_storage_root_h_val_cong:
  assumes frame: "\<And>a. a \<in> raw_xlist_storage lp xs \<Longrightarrow>
      h' a = h a"
  shows "h_val h' lp = h_val h lp"
  apply (rule delay_h_val_region_cong)
  apply (rule frame)
  by (simp add: raw_xlist_storage_def raw_list_region_def)

lemma delay_storage_item_h_val_cong:
  assumes frame: "\<And>a. a \<in> raw_xlist_storage lp xs \<Longrightarrow>
      h' a = h a"
    and member: "p \<in> set (ring xs)"
  shows "h_val h' p = h_val h p"
  apply (rule delay_h_val_region_cong)
  apply (rule frame)
  using member by (auto simp: raw_xlist_storage_def raw_item_region_def)

lemma delay_raw_next_at_cong:
  assumes root_same: "h_val h' lp = h_val h lp"
    and item_same:
      "\<And>p. p \<in> set rs \<Longrightarrow> h_val h' p = h_val h p"
    and cycle: "p \<in> insert (raw_end_item lp) (set rs)"
  shows "raw_next_at h' lp p = raw_next_at h lp p"
  using cycle root_same item_same
  by (auto simp: raw_next_at_def)

lemma delay_raw_prev_at_cong:
  assumes root_same: "h_val h' lp = h_val h lp"
    and item_same:
      "\<And>p. p \<in> set rs \<Longrightarrow> h_val h' p = h_val h p"
    and cycle: "p \<in> insert (raw_end_item lp) (set rs)"
  shows "raw_prev_at h' lp p = raw_prev_at h lp p"
  using cycle root_same item_same
  by (auto simp: raw_prev_at_def)

lemma delay_raw_edge_pair_in_cycle:
  assumes edge: "(p,q) \<in> set (raw_edge_pairs lp rs)"
  shows
    "p \<in> insert (raw_end_item lp) (set rs) \<and>
     q \<in> insert (raw_end_item lp) (set rs)"
proof -
  have left: "p \<in> set (raw_end_item lp # rs)"
    by (rule in_set_zip1; use edge in \<open>simp add: raw_edge_pairs_def\<close>)
  have right: "q \<in> set (rs @ [raw_end_item lp])"
    by (rule in_set_zip2; use edge in \<open>simp add: raw_edge_pairs_def\<close>)
  show ?thesis using left right by auto
qed

lemma delay_raw_ring_links_h_val_cong:
  assumes links: "raw_ring_links h lp rs"
    and root_same: "h_val h' lp = h_val h lp"
    and item_same:
      "\<And>p. p \<in> set rs \<Longrightarrow> h_val h' p = h_val h p"
  shows "raw_ring_links h' lp rs"
proof -
  have old:
    "\<And>p q. (p,q) \<in> set (raw_edge_pairs lp rs) \<Longrightarrow>
       raw_next_at h lp p = q \<and> raw_prev_at h lp q = p"
    using links by (auto simp: raw_ring_links_def list_all_iff)
  show ?thesis
    unfolding raw_ring_links_def list_all_iff
  proof (intro ballI)
    fix edge
    assume edge_mem: "edge \<in> set (raw_edge_pairs lp rs)"
    obtain p q where edge_eq: "edge = (p,q)" by (cases edge)
    have cycle:
      "p \<in> insert (raw_end_item lp) (set rs) \<and>
       q \<in> insert (raw_end_item lp) (set rs)"
      using delay_raw_edge_pair_in_cycle[of p q lp rs]
        edge_mem edge_eq by simp
    have next_same:
      "raw_next_at h' lp p = raw_next_at h lp p"
      by (rule delay_raw_next_at_cong[OF root_same item_same]; use cycle in blast)
    have previous:
      "raw_prev_at h' lp q = raw_prev_at h lp q"
      by (rule delay_raw_prev_at_cong[OF root_same item_same]; use cycle in blast)
    show "case edge of (p,q) \<Rightarrow>
        raw_next_at h' lp p = q \<and> raw_prev_at h' lp q = p"
      using old[of p q] edge_mem edge_eq next_same previous by simp
  qed
qed

theorem delay_raw_xlist_rel_h_val_cong:
  assumes rel: "raw_xlist_rel h lp xs"
    and root_same: "h_val h' lp = h_val h lp"
    and item_same:
      "\<And>p. p \<in> set (ring xs) \<Longrightarrow> h_val h' p = h_val h p"
  shows "raw_xlist_rel h' lp xs"
proof -
  have links:
    "raw_ring_links h' lp (ring xs)"
    by (rule delay_raw_ring_links_h_val_cong[
          OF _ root_same item_same])
       (use rel in \<open>simp add: raw_xlist_rel_def raw_xlist_view_def\<close>)
  show ?thesis
    using rel root_same item_same links
    by (auto simp: raw_xlist_rel_def raw_xlist_view_def
        raw_cursor_at_def raw_key_at_def)
qed

theorem delay_raw_xlist_rel_storage_frame:
  assumes rel: "raw_xlist_rel h lp xs"
    and frame: "\<And>a. a \<in> raw_xlist_storage lp xs \<Longrightarrow>
      h' a = h a"
  shows "raw_xlist_rel h' lp xs"
proof (rule delay_raw_xlist_rel_h_val_cong[OF rel])
  show "h_val h' lp = h_val h lp"
    by (rule delay_storage_root_h_val_cong[OF frame])
next
  fix p
  assume member: "p \<in> set (ring xs)"
  show "h_val h' p = h_val h p"
    by (rule delay_storage_item_h_val_cong[OF frame member])
qed

lemma delay_raw_ordered_xlist_rel_h_val_cong:
  assumes ordered: "raw_ordered_xlist_rel h lp xs"
    and root_same: "h_val h' lp = h_val h lp"
    and item_same:
      "\<And>p. p \<in> set (ring xs) \<Longrightarrow> h_val h' p = h_val h p"
  shows "raw_ordered_xlist_rel h' lp xs"
proof -
  have raw: "raw_xlist_rel h lp xs"
    and sentinel: "raw_sentinel_max h lp"
    using ordered by (simp_all add: raw_ordered_xlist_rel_def)
  have raw': "raw_xlist_rel h' lp xs"
    by (rule delay_raw_xlist_rel_h_val_cong[OF raw root_same item_same])
  have sentinel_key:
    "raw_key_at h' (raw_end_item lp) =
     raw_key_at h (raw_end_item lp)"
    by (rule raw_ordered_sentinel_key_cong[OF root_same])
  have sentinel': "raw_sentinel_max h' lp"
    using sentinel sentinel_key by (simp add: raw_sentinel_max_def)
  show ?thesis
    using ordered raw' sentinel'
    by (simp add: raw_ordered_xlist_rel_def)
qed

theorem delay_raw_ordered_xlist_rel_storage_frame:
  assumes ordered: "raw_ordered_xlist_rel h lp xs"
    and frame: "\<And>a. a \<in> raw_xlist_storage lp xs \<Longrightarrow>
      h' a = h a"
  shows "raw_ordered_xlist_rel h' lp xs"
proof (rule delay_raw_ordered_xlist_rel_h_val_cong[OF ordered])
  show "h_val h' lp = h_val h lp"
    by (rule delay_storage_root_h_val_cong[OF frame])
next
  fix p
  assume member: "p \<in> set (ring xs)"
  show "h_val h' p = h_val h p"
    by (rule delay_storage_item_h_val_cong[OF frame member])
qed

definition scheduler_delay_selected_list ::
  "Scheduler_V611_Parse.globals \<Rightarrow> 32 word \<Rightarrow>
   Scheduler_V611_Parse.xLIST_C ptr"
where
  "scheduler_delay_selected_list s ticks =
     (let wake = Scheduler_V611_Parse.globals.xTickCount_' s + ticks
      in if wake < Scheduler_V611_Parse.globals.xTickCount_' s
         then Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_' s
         else Scheduler_V611_Parse.globals.pxDelayedTaskList_' s)"

definition scheduler_delay_selected_root ::
  "Scheduler_V611_Parse.globals \<Rightarrow> 32 word \<Rightarrow> xLIST_C ptr"
where
  "scheduler_delay_selected_root s ticks =
     abi_list_ptr (scheduler_delay_selected_list s ticks)"

definition scheduler_delay_remove_key_insert_heap ::
  "heap_mem \<Rightarrow> Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   32 word \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow> heap_mem"
where
  "scheduler_delay_remove_key_insert_heap h tp wake target xs =
     (let p = abi_generic_list_item_ptr tp;
          hr = raw_remove_concrete_heap h p;
          hk = scheduler_generic_item_key_heap hr tp wake
      in raw_ordered_insert_general_heap hk target xs p)"

definition scheduler_delay_remove_key_insert' ::
  "Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow> 32 word \<Rightarrow>
   Scheduler_V611_Parse.xLIST_C ptr \<Rightarrow>
   (unit, Scheduler_V611_Parse.globals) res_monad"
where
  "scheduler_delay_remove_key_insert' tp wake target = do {
     Scheduler_V611_Delay_Translation.vListRemove'
       (scheduler_generic_item_ptr tp);
     modify (\<lambda>s.
       scheduler_mem_state
         (scheduler_generic_item_key_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)) tp wake) s);
     Scheduler_V611_Delay_Translation.vListInsert' target
       (scheduler_generic_item_ptr tp)
   }"

text \<open>
  The representation used by the universal core has one explicit source-entry
  ownership fact.  It is not a fixed priority or a chosen list slot: owner is
  the ready root determined by the current task and its arbitrary abstract
  priority.  A later scheduler-relation theorem must derive this fact from
  settled_wf plus a family relabelling relation.  raw_scheduler_rel alone is
  intentionally too weak, because core_wf only says that the current task is
  live and does not put its Generic node in a ready ring.
\<close>

definition scheduler_delay_owner_entry_rel ::
  "heap_mem \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow> bool"
where
  "scheduler_delay_owner_entry_rel h roots fam owner p \<longleftrightarrow>
     owner \<in> roots \<and>
     raw_family_members roots fam p = {owner} \<and>
     p \<in> set (ring (fam owner)) \<and>
     pvContainer_C (h_val h p) = PTR_COERCE(xLIST_C \<rightarrow> unit) owner"

theorem scheduler_settled_current_ready_rawE:
  assumes raw: "raw_scheduler_rel D R s a"
    and settled: "settled_wf a"
    and current: "sa_current a = Some t"
  obtains xs where
    "raw_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
       (abi_list_ptr (sr_ready R (sa_priority a t))) xs"
    "abi_generic_list_item_ptr (sd_tcb_ptr D t) \<in> set (ring xs)"
proof -
  have decode: "scheduler_decode_rel D a"
    and lists: "scheduler_lists_rel D R s a"
    and core: "core_wf a"
    using raw by (auto simp: raw_scheduler_rel_def)
  have live: "t \<in> sa_live a"
    by (rule core_wf_current_is_live[OF core current])
  have priority: "sa_priority a t < 4"
    using core live by (auto simp: core_wf_def)
  have abstract_member:
    "Generic t \<in> set (ring (sa_ready a (sa_priority a t)))"
    using settled current by (simp add: settled_wf_def)
  have sched:
    "sched_xlist_rel (sd_node_decode D)
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
       (abi_list_ptr (sr_ready R (sa_priority a t)))
       (sa_ready a (sa_priority a t))"
    using lists priority
    by (simp add: scheduler_lists_rel_def Let_def)
  then obtain xs where
      raw_xs:
        "raw_xlist_rel
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
           (abi_list_ptr (sr_ready R (sa_priority a t))) xs"
    and relabel:
        "xlist_relabel (sd_node_decode D) xs
           (sa_ready a (sa_priority a t))"
    by (auto simp: sched_xlist_rel_def)
  from xlist_relabel_decoder_right_closed[OF relabel abstract_member]
  obtain q where q_member: "q \<in> set (ring xs)"
    and q_decode: "sd_node_decode D q = Some (Generic t)"
    by blast
  have q_eq: "q = abi_generic_list_item_ptr (sd_tcb_ptr D t)"
    using scheduler_node_decode_Generic_iff[OF decode, of q t]
      q_decode by simp
  show thesis
    by (rule that[OF raw_xs]) (use q_member q_eq in simp)
qed

corollary scheduler_settled_current_tcb_and_ready_rawE:
  assumes raw: "raw_scheduler_rel D R s a"
    and settled: "settled_wf a"
  obtains t xs where
    "sa_current a = Some t"
    "Scheduler_V611_Parse.globals.pxCurrentTCB_' s = sd_tcb_ptr D t"
    "raw_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
       (abi_list_ptr (sr_ready R (sa_priority a t))) xs"
    "abi_generic_list_item_ptr (sd_tcb_ptr D t) \<in> set (ring xs)"
proof -
  obtain t where current: "sa_current a = Some t"
    using settled by (auto simp: settled_wf_def split: option.splits)
  have current_tcb:
    "Scheduler_V611_Parse.globals.pxCurrentTCB_' s = sd_tcb_ptr D t"
    using raw current
    by (simp add: raw_scheduler_rel_def scheduler_current_rel_def)
  from scheduler_settled_current_ready_rawE[OF raw settled current]
  obtain xs where raw_xs:
      "raw_xlist_rel
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
         (abi_list_ptr (sr_ready R (sa_priority a t))) xs"
    and member:
      "abi_generic_list_item_ptr (sd_tcb_ptr D t) \<in> set (ring xs)" .
  show thesis by (rule that[OF current current_tcb raw_xs member])
qed

lemma scheduler_delay_owner_entry_member:
  assumes entry: "scheduler_delay_owner_entry_rel h roots fam owner p"
  shows "p \<in> set (ring (fam owner))"
  using entry by (simp add: scheduler_delay_owner_entry_rel_def)

lemma scheduler_delay_owner_entry_absent_other:
  assumes entry: "scheduler_delay_owner_entry_rel h roots fam owner p"
    and other: "other \<in> roots"
    and distinct: "other \<noteq> owner"
  shows "p \<notin> set (ring (fam other))"
  using entry other distinct
  by (auto simp: scheduler_delay_owner_entry_rel_def raw_family_members_def)

theorem scheduler_delay_remove_preserves_nonowner_ordered:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and owner_entry:
      "scheduler_delay_owner_entry_rel h roots fam owner p"
    and target: "target \<in> roots"
    and distinct: "owner \<noteq> target"
    and ordered: "raw_ordered_xlist_rel h target (fam target)"
  shows
    "raw_ordered_xlist_rel (raw_remove_concrete_heap h p)
       target (fam target)"
proof (rule delay_raw_ordered_xlist_rel_storage_frame[OF ordered])
  fix a
  assume address: "a \<in> raw_xlist_storage target (fam target)"
  have owner_root: "owner \<in> roots"
    and member: "p \<in> set (ring (fam owner))"
    using owner_entry
    by (simp_all add: scheduler_delay_owner_entry_rel_def)
  show "raw_remove_concrete_heap h p a = h a"
    by (rule raw_remove_family_non_target_byte_frame[
          OF pre owner_root target distinct member address])
qed

lemma scheduler_delay_wake_key_preserves_disjoint_item:
  assumes guard: "c_guard (abi_generic_list_item_ptr tp)"
    and disjoint:
      "raw_item_region (abi_generic_list_item_ptr tp) \<inter>
       raw_item_region q = {}"
  shows
    "h_val (scheduler_generic_item_key_heap h tp wake) q = h_val h q"
  apply (subst scheduler_generic_item_key_heap_raw_whole[OF guard])
  by (rule raw_item_update_preserves_disjoint_item[OF disjoint])

theorem scheduler_delay_wake_key_preserves_target_ordered:
  fixes tp :: "Scheduler_V611_Parse.tskTaskControlBlock_C ptr"
  defines "p \<equiv> abi_generic_list_item_ptr tp"
  assumes ordered: "raw_ordered_xlist_rel h target xs"
    and geometry: "raw_family_insert_geometry roots fam p"
    and target: "target \<in> roots"
    and ring: "ring xs = ring (fam target)"
    and absent: "p \<notin> set (ring (fam target))"
  shows
    "raw_ordered_xlist_rel
       (scheduler_generic_item_key_heap h tp wake) target xs"
proof (rule delay_raw_ordered_xlist_rel_h_val_cong[OF ordered])
  have guard: "c_guard p"
    and root_disjoint:
      "raw_item_region p \<inter> raw_list_region target = {}"
    and item_disjoint:
      "\<And>q. q \<in> set (ring (fam target)) \<Longrightarrow>
        q \<noteq> p \<Longrightarrow>
        raw_item_region p \<inter> raw_item_region q = {}"
    using geometry target
    by (auto simp: raw_family_insert_geometry_def)
  show
    "h_val (scheduler_generic_item_key_heap h tp wake) target =
     h_val h target"
  proof -
    have guard': "c_guard (abi_generic_list_item_ptr tp)"
      using guard by (simp add: p_def)
    have disjoint':
      "raw_item_region (abi_generic_list_item_ptr tp) \<inter>
       raw_list_region target = {}"
      using root_disjoint by (simp add: p_def)
    show ?thesis
      by (rule scheduler_generic_item_key_heap_raw_root_frame[
            OF guard' disjoint'])
  qed
next
  fix q
  assume q: "q \<in> set (ring xs)"
  have guard: "c_guard p"
    and disjoint_if:
      "\<And>r. r \<in> set (ring (fam target)) \<Longrightarrow>
        r \<noteq> p \<Longrightarrow>
        raw_item_region p \<inter> raw_item_region r = {}"
    using geometry target
    by (auto simp: raw_family_insert_geometry_def)
  have q_fam: "q \<in> set (ring (fam target))"
    using q ring by simp
  have q_ne: "q \<noteq> p" using q_fam absent by blast
  have disjoint: "raw_item_region p \<inter> raw_item_region q = {}"
    by (rule disjoint_if[OF q_fam q_ne])
  show
    "h_val (scheduler_generic_item_key_heap h tp wake) q = h_val h q"
  proof -
    have guard': "c_guard (abi_generic_list_item_ptr tp)"
      using guard by (simp add: p_def)
    have disjoint':
      "raw_item_region (abi_generic_list_item_ptr tp) \<inter>
       raw_item_region q = {}"
      using disjoint by (simp add: p_def)
    show ?thesis
      by (rule scheduler_delay_wake_key_preserves_disjoint_item[
            OF guard' disjoint'])
  qed
qed

theorem scheduler_delay_entry_fresh_for_derived_target:
  assumes owner_entry:
      "scheduler_delay_owner_entry_rel h roots fam owner p"
    and geometry: "raw_family_insert_geometry roots fam p"
    and target: "target \<in> roots"
    and distinct: "owner \<noteq> target"
  shows "raw_fresh_for_insert target (ring (fam target)) p"
proof -
  have absent: "p \<notin> set (ring (fam target))"
    by (rule scheduler_delay_owner_entry_absent_other[
          OF owner_entry target distinct[symmetric]])
  have guard: "c_guard p"
    and not_end: "p \<noteq> raw_end_item target"
    and root_disjoint:
      "raw_item_region p \<inter> raw_list_region target = {}"
    and items:
      "\<forall>q\<in>set (ring (fam target)).
        q \<noteq> p \<longrightarrow>
        raw_item_region p \<inter> raw_item_region q = {}"
    using geometry target
    by (auto simp: raw_family_insert_geometry_def)
  show ?thesis
    using guard not_end absent root_disjoint items
    by (auto simp: raw_fresh_for_insert_def)
qed

theorem scheduler_delay_remove_wake_target_ready:
  fixes tp :: "Scheduler_V611_Parse.tskTaskControlBlock_C ptr"
    and p :: raw_node_id
    and h hr hk :: heap_mem
    and wake :: "32 word"
  defines "p \<equiv> abi_generic_list_item_ptr tp"
    and "hr \<equiv> raw_remove_concrete_heap h p"
    and "hk \<equiv> scheduler_generic_item_key_heap hr tp wake"
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and owner_entry:
      "scheduler_delay_owner_entry_rel h roots fam owner p"
    and geometry: "raw_family_insert_geometry roots fam p"
    and target: "target \<in> roots"
    and distinct: "owner \<noteq> target"
    and ordered: "raw_ordered_xlist_rel h target (fam target)"
  shows
    "raw_ordered_xlist_rel hk target (fam target) \<and>
     raw_fresh_for_insert target (ring (fam target)) p"
proof -
  have after_remove:
    "raw_ordered_xlist_rel hr target (fam target)"
    unfolding hr_def
    by (rule scheduler_delay_remove_preserves_nonowner_ordered[
          OF pre owner_entry target distinct ordered])
  have after_key:
    "raw_ordered_xlist_rel hk target (fam target)"
  proof -
    have absent: "p \<notin> set (ring (fam target))"
      by (rule scheduler_delay_owner_entry_absent_other[
            OF owner_entry target distinct[symmetric]])
    have geometry':
      "raw_family_insert_geometry roots fam
         (abi_generic_list_item_ptr tp)"
      using geometry by (simp add: p_def)
    have absent':
      "abi_generic_list_item_ptr tp \<notin> set (ring (fam target))"
      using absent by (simp add: p_def)
    have preserved:
      "raw_ordered_xlist_rel
         (scheduler_generic_item_key_heap hr tp wake)
         target (fam target)"
      by (rule scheduler_delay_wake_key_preserves_target_ordered[
            OF after_remove geometry' target refl absent'])
    show ?thesis using preserved by (simp add: hk_def)
  qed
  have fresh: "raw_fresh_for_insert target (ring (fam target)) p"
    by (rule scheduler_delay_entry_fresh_for_derived_target[
          OF owner_entry geometry target distinct])
  show ?thesis using after_key fresh by blast
qed

theorem scheduler_delay_remove_key_insert_exact_state:
  fixes s :: Scheduler_V611_Parse.globals
    and tp :: "Scheduler_V611_Parse.tskTaskControlBlock_C ptr"
    and owner_lp target_lp :: "Scheduler_V611_Parse.xLIST_C ptr"
    and p :: raw_node_id
    and owner target :: "xLIST_C ptr"
    and h hr hk hf :: heap_mem
    and wake :: "32 word"
    and fam :: "xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs"
  defines "h \<equiv> hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)"
    and "p \<equiv> abi_generic_list_item_ptr tp"
    and "owner \<equiv> abi_list_ptr owner_lp"
    and "target \<equiv> abi_list_ptr target_lp"
    and "hr \<equiv> raw_remove_concrete_heap h p"
    and "hk \<equiv> scheduler_generic_item_key_heap hr tp wake"
    and "hf \<equiv>
      raw_ordered_insert_general_heap hk target (fam target) p"
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and owner_entry:
      "scheduler_delay_owner_entry_rel h roots fam owner p"
    and geometry: "raw_family_insert_geometry roots fam p"
    and target_root: "target \<in> roots"
    and owner_target: "owner \<noteq> target"
    and target_ordered:
      "raw_ordered_xlist_rel h target (fam target)"
  shows
    "scheduler_delay_remove_key_insert' tp wake target_lp \<bullet> s
     \<lbrace>\<lambda>r t. r = Result () \<and> t = scheduler_mem_state hf s\<rbrace>"
proof -
  have owner_rel: "raw_xlist_rel h owner (fam owner)"
    using pre owner_entry
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def
        scheduler_delay_owner_entry_rel_def)
  have member: "p \<in> set (ring (fam owner))"
    by (rule scheduler_delay_owner_entry_member[OF owner_entry])
  have remove_exact:
    "Scheduler_V611_Delay_Translation.vListRemove'
       (scheduler_generic_item_ptr tp) \<bullet> s
     \<lbrace>\<lambda>r t. r = Result () \<and> t = scheduler_mem_state hr s\<rbrace>"
  proof -
    have source_rel:
      "raw_xlist_rel
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
         (abi_list_ptr owner_lp) (fam owner)"
      using owner_rel by (simp add: h_def owner_def)
    have source_member:
      "abi_item_ptr (scheduler_generic_item_ptr tp) \<in>
         set (ring (fam owner))"
      using member
      by (simp add: p_def scheduler_generic_item_ptr_def
          abi_generic_list_item_ptr_def)
    have execution:
      "Scheduler_V611_Delay_Translation.vListRemove'
         (scheduler_generic_item_ptr tp) \<bullet> s
       \<lbrace>\<lambda>r t. r = Result () \<and>
          t = scheduler_mem_state
            (raw_remove_concrete_heap
              (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
              (abi_item_ptr (scheduler_generic_item_ptr tp))) s\<rbrace>"
      by (rule scheduler_vListRemove_general_exact_state[
            OF source_rel source_member])
    show ?thesis
      apply (rule runs_to_weaken[OF execution])
      by (simp add: hr_def h_def p_def scheduler_generic_item_ptr_def
          abi_generic_list_item_ptr_def)
  qed
  have ready:
    "raw_ordered_xlist_rel hk target (fam target) \<and>
     raw_fresh_for_insert target (ring (fam target)) p"
  proof -
    have owner_entry':
      "scheduler_delay_owner_entry_rel h roots fam owner
         (abi_generic_list_item_ptr tp)"
      using owner_entry by (simp add: p_def)
    have geometry':
      "raw_family_insert_geometry roots fam
         (abi_generic_list_item_ptr tp)"
      using geometry by (simp add: p_def)
    have ready':
      "raw_ordered_xlist_rel
         (scheduler_generic_item_key_heap
           (raw_remove_concrete_heap h (abi_generic_list_item_ptr tp))
           tp wake)
         target (fam target) \<and>
       raw_fresh_for_insert target (ring (fam target))
         (abi_generic_list_item_ptr tp)"
      by (rule scheduler_delay_remove_wake_target_ready[
            OF pre owner_entry' geometry' target_root owner_target
               target_ordered])
    show ?thesis using ready'
      by (simp add: hk_def hr_def p_def)
  qed
  have insert_exact:
    "Scheduler_V611_Delay_Translation.vListInsert' target_lp
       (scheduler_generic_item_ptr tp) \<bullet> (scheduler_mem_state hk s)
     \<lbrace>\<lambda>r t. r = Result () \<and> t = scheduler_mem_state hf s\<rbrace>"
  proof -
    have source_ordered:
      "raw_ordered_xlist_rel
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
           (scheduler_mem_state hk s)))
         (abi_list_ptr target_lp) (fam target)"
      using ready[THEN conjunct1]
      by (simp add: target_def)
    have source_fresh:
      "raw_fresh_for_insert (abi_list_ptr target_lp)
         (ring (fam target))
         (abi_item_ptr (scheduler_generic_item_ptr tp))"
      using ready[THEN conjunct2]
      by (simp add: target_def p_def scheduler_generic_item_ptr_def
          abi_generic_list_item_ptr_def)
    have source_execution:
      "Scheduler_V611_Delay_Translation.vListInsert' target_lp
         (scheduler_generic_item_ptr tp) \<bullet> (scheduler_mem_state hk s)
       \<lbrace>\<lambda>r t. r = Result () \<and>
          t = scheduler_mem_state
            (raw_ordered_insert_general_heap
              (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
                (scheduler_mem_state hk s)))
              (abi_list_ptr target_lp) (fam target)
              (abi_item_ptr (scheduler_generic_item_ptr tp)))
            (scheduler_mem_state hk s)\<rbrace>"
      by (rule scheduler_vListInsert_ordered_general_exact_state[
            OF source_ordered source_fresh])
    have execution:
      "Scheduler_V611_Delay_Translation.vListInsert' target_lp
         (scheduler_generic_item_ptr tp) \<bullet> (scheduler_mem_state hk s)
       \<lbrace>\<lambda>r t. r = Result () \<and>
          t = scheduler_mem_state
            (raw_ordered_insert_general_heap hk target
              (fam target) p) (scheduler_mem_state hk s)\<rbrace>"
      apply (rule runs_to_weaken[OF source_execution])
      by (simp add: target_def p_def scheduler_generic_item_ptr_def
          abi_generic_list_item_ptr_def)
    show ?thesis
      apply (rule runs_to_weaken[OF execution])
      by (simp add: hf_def)
  qed
  show ?thesis
    unfolding scheduler_delay_remove_key_insert'_def
    apply runs_to_vcg
    apply (rule runs_to_weaken[OF remove_exact])
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[OF insert_exact[unfolded hk_def]])
    apply (simp add: hk_def hr_def h_def scheduler_mem_state_def)
    done
qed

theorem scheduler_delay_remove_wake_derived_target_ready:
  fixes s :: Scheduler_V611_Parse.globals
    and tp :: "Scheduler_V611_Parse.tskTaskControlBlock_C ptr"
    and p :: raw_node_id
    and current overflow target :: "xLIST_C ptr"
    and h hr hk :: heap_mem
    and ticks wake :: "32 word"
    and fam :: "xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs"
  defines "p \<equiv> abi_generic_list_item_ptr tp"
    and "wake \<equiv> Scheduler_V611_Parse.globals.xTickCount_' s + ticks"
    and "current \<equiv>
      abi_list_ptr (Scheduler_V611_Parse.globals.pxDelayedTaskList_' s)"
    and "overflow \<equiv>
      abi_list_ptr (Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_' s)"
    and "target \<equiv> scheduler_delay_selected_root s ticks"
    and "hr \<equiv> raw_remove_concrete_heap h p"
    and "hk \<equiv> scheduler_generic_item_key_heap hr tp wake"
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and owner_entry:
      "scheduler_delay_owner_entry_rel h roots fam owner p"
    and geometry: "raw_family_insert_geometry roots fam p"
    and current_root: "current \<in> roots"
    and overflow_root: "overflow \<in> roots"
    and owner_current: "owner \<noteq> current"
    and owner_overflow: "owner \<noteq> overflow"
    and current_ordered:
      "raw_ordered_xlist_rel h current (fam current)"
    and overflow_ordered:
      "raw_ordered_xlist_rel h overflow (fam overflow)"
  shows
    "target \<in> roots \<and>
     owner \<noteq> target \<and>
     raw_ordered_xlist_rel hk target (fam target) \<and>
     raw_fresh_for_insert target (ring (fam target)) p"
proof -
  have target_cases: "target = current \<or> target = overflow"
    unfolding target_def current_def overflow_def
      scheduler_delay_selected_root_def scheduler_delay_selected_list_def
      wake_def
    by (simp add: Let_def)
  have target_root: "target \<in> roots"
    using target_cases current_root overflow_root by blast
  have owner_target: "owner \<noteq> target"
    using target_cases owner_current owner_overflow by blast
  have target_ordered:
    "raw_ordered_xlist_rel h target (fam target)"
    using target_cases current_ordered overflow_ordered by blast
  have ready:
    "raw_ordered_xlist_rel hk target (fam target) \<and>
     raw_fresh_for_insert target (ring (fam target)) p"
  proof -
    have owner_entry':
      "scheduler_delay_owner_entry_rel h roots fam owner
         (abi_generic_list_item_ptr tp)"
      using owner_entry by (simp add: p_def)
    have geometry':
      "raw_family_insert_geometry roots fam
         (abi_generic_list_item_ptr tp)"
      using geometry by (simp add: p_def)
    have ready':
      "raw_ordered_xlist_rel
         (scheduler_generic_item_key_heap
           (raw_remove_concrete_heap h (abi_generic_list_item_ptr tp))
           tp wake)
         target (fam target) \<and>
       raw_fresh_for_insert target (ring (fam target))
         (abi_generic_list_item_ptr tp)"
      by (rule scheduler_delay_remove_wake_target_ready[
            OF pre owner_entry' geometry' target_root owner_target
               target_ordered])
    show ?thesis using ready'
      by (simp add: hk_def hr_def p_def)
  qed
  show ?thesis using target_root owner_target ready by blast
qed

corollary scheduler_delay_remove_key_insert_derived_exact_state:
  fixes s :: Scheduler_V611_Parse.globals
    and tp :: "Scheduler_V611_Parse.tskTaskControlBlock_C ptr"
    and owner_lp :: "Scheduler_V611_Parse.xLIST_C ptr"
    and target_lp :: "Scheduler_V611_Parse.xLIST_C ptr"
    and p :: raw_node_id
    and owner current overflow target :: "xLIST_C ptr"
    and h hr hk hf :: heap_mem
    and ticks wake :: "32 word"
    and fam :: "xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs"
  defines "h \<equiv> hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)"
    and "p \<equiv> abi_generic_list_item_ptr tp"
    and "owner \<equiv> abi_list_ptr owner_lp"
    and "wake \<equiv> Scheduler_V611_Parse.globals.xTickCount_' s + ticks"
    and "current \<equiv>
      abi_list_ptr (Scheduler_V611_Parse.globals.pxDelayedTaskList_' s)"
    and "overflow \<equiv>
      abi_list_ptr (Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_' s)"
    and "target_lp \<equiv> scheduler_delay_selected_list s ticks"
    and "target \<equiv> abi_list_ptr target_lp"
    and "hr \<equiv> raw_remove_concrete_heap h p"
    and "hk \<equiv> scheduler_generic_item_key_heap hr tp wake"
    and "hf \<equiv>
      raw_ordered_insert_general_heap hk target (fam target) p"
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and owner_entry:
      "scheduler_delay_owner_entry_rel h roots fam owner p"
    and geometry: "raw_family_insert_geometry roots fam p"
    and current_root: "current \<in> roots"
    and overflow_root: "overflow \<in> roots"
    and owner_current: "owner \<noteq> current"
    and owner_overflow: "owner \<noteq> overflow"
    and current_ordered:
      "raw_ordered_xlist_rel h current (fam current)"
    and overflow_ordered:
      "raw_ordered_xlist_rel h overflow (fam overflow)"
  shows
    "scheduler_delay_remove_key_insert' tp wake target_lp \<bullet> s
     \<lbrace>\<lambda>r t. r = Result () \<and> t = scheduler_mem_state hf s\<rbrace>"
proof -
  have target_eq:
    "target = scheduler_delay_selected_root s ticks"
    by (simp add: target_def target_lp_def
        scheduler_delay_selected_root_def)
  have derived:
    "target \<in> roots \<and>
     owner \<noteq> target \<and>
     raw_ordered_xlist_rel hk target (fam target) \<and>
     raw_fresh_for_insert target (ring (fam target)) p"
    using scheduler_delay_remove_wake_derived_target_ready[
      where s=s and tp=tp and ticks=ticks and h=h and roots=roots
        and fam=fam and live=live and D=D and owner=owner]
      pre owner_entry geometry current_root overflow_root owner_current
      owner_overflow current_ordered overflow_ordered
    unfolding p_def wake_def current_def overflow_def target_eq
      hr_def hk_def
    by blast
  have target_root: "target \<in> roots"
    and owner_target: "owner \<noteq> target"
    using derived by blast+
  have target_cases: "target = current \<or> target = overflow"
    unfolding target_def target_lp_def current_def overflow_def
      scheduler_delay_selected_list_def
    by (simp add: Let_def)
  have target_ordered_entry:
    "raw_ordered_xlist_rel h target (fam target)"
    using target_cases current_ordered overflow_ordered by blast
  have pre_source:
    "scheduler_family_pre_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
       roots fam live D"
    using pre by (simp add: h_def)
  have owner_entry_source:
    "scheduler_delay_owner_entry_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
       roots fam (abi_list_ptr owner_lp)
       (abi_generic_list_item_ptr tp)"
    using owner_entry by (simp add: h_def owner_def p_def)
  have geometry_source:
    "raw_family_insert_geometry roots fam
       (abi_generic_list_item_ptr tp)"
    using geometry by (simp add: p_def)
  have target_root_source:
    "abi_list_ptr target_lp \<in> roots"
    using target_root by (simp add: target_def)
  have owner_target_source:
    "abi_list_ptr owner_lp \<noteq> abi_list_ptr target_lp"
    using owner_target by (simp add: owner_def target_def)
  have target_ordered_source:
    "raw_ordered_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
       (abi_list_ptr target_lp) (fam (abi_list_ptr target_lp))"
    using target_ordered_entry by (simp add: h_def target_def)
  have source_execution:
    "scheduler_delay_remove_key_insert' tp wake target_lp \<bullet> s
     \<lbrace>\<lambda>r t. r = Result () \<and>
       t = scheduler_mem_state
         (raw_ordered_insert_general_heap
           (scheduler_generic_item_key_heap
             (raw_remove_concrete_heap
               (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
               (abi_generic_list_item_ptr tp)) tp wake)
           (abi_list_ptr target_lp) (fam (abi_list_ptr target_lp))
           (abi_generic_list_item_ptr tp)) s\<rbrace>"
    by (rule scheduler_delay_remove_key_insert_exact_state[
          OF pre_source owner_entry_source geometry_source
             target_root_source owner_target_source target_ordered_source])
  show ?thesis
    apply (rule runs_to_weaken[OF source_execution])
    by (simp add: hf_def hk_def hr_def h_def p_def target_def)
qed

text \<open>
  At this boundary the generated remove and ordered-insert theorems can be
  composed with no post-shaped assumptions.  The only remaining source-level
  work is syntactic VCG plumbing for the current-TCB guards and the nested
  wake-key field update.  Both possible delayed roots must satisfy the entry
  premises; the actual target below remains the derived expression
  scheduler_delay_selected_root s ticks.
\<close>

end
