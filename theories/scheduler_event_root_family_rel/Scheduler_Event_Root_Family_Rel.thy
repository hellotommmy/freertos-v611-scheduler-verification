theory Scheduler_Event_Root_Family_Rel
  imports
    "EAL6_FreeRTOS_V611_Scheduler_List_Family_Frame_Capstone.Scheduler_List_Family_Frame_Capstone"
    "EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Insert_Sequence.List_V611_Raw_R6_Remove_Insert_Sequence"
begin

text \<open>
  Universal finite Event-root-family representation for the scheduler.

  The parameters remain arbitrary throughout: the finite live-task set, the
  finite root set, the distinguished pending-ready root, every ring length and
  cursor, every task identity, every address, and every Event payload key.
  K_E is a total function on task identities and is constrained at every live
  task's physical xEventListItem whether that item is linked or unlinked.

  This is an entry representation invariant, not a postcondition disguised as
  a premise.  It simultaneously records the physical raw rings, their abstract
  Event-only relabellings, exact root ownership through pvContainer, unique
  family membership, and the payload map needed by later remove/insert and
  scheduler-refinement layers.
\<close>

definition event_item_raw_ptr ::
  "'tid scheduler_decode \<Rightarrow> 'tid \<Rightarrow> raw_node_id"
where
  "event_item_raw_ptr D t =
     abi_event_list_item_ptr (sd_tcb_ptr D t)"

definition event_item_raw_set ::
  "'tid set \<Rightarrow> 'tid scheduler_decode \<Rightarrow> raw_node_id set"
where
  "event_item_raw_set live D = event_item_raw_ptr D ` live"

definition event_external_roots ::
  "xLIST_C ptr set \<Rightarrow> xLIST_C ptr \<Rightarrow> xLIST_C ptr set"
where
  "event_external_roots roots pending = roots - {pending}"

definition event_family_root_rep ::
  "'tid scheduler_decode \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   'tid set \<Rightarrow> xLIST_C ptr \<Rightarrow> bool"
where
  "event_family_root_rep D raw_fam abs_fam live lp \<longleftrightarrow>
     set (ring (raw_fam lp)) \<subseteq> event_item_raw_set live D \<and>
     xlist_relabel (sd_node_decode D) (raw_fam lp) (abs_fam lp) \<and>
     xlist_wf (abs_fam lp) \<and>
     event_ring (abs_fam lp)"

definition event_family_container_rep ::
  "'tid scheduler_decode \<Rightarrow> heap_mem \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   'tid set \<Rightarrow> bool"
where
  "event_family_container_rep D h roots raw_fam live \<longleftrightarrow>
     raw_family_container_faithful_on h roots raw_fam
       (event_item_raw_set live D) \<and>
     (\<forall>t\<in>live. \<forall>lp\<in>roots.
        event_item_raw_ptr D t \<in> set (ring (raw_fam lp)) \<longleftrightarrow>
        pvContainer_C (h_val h (event_item_raw_ptr D t)) =
          PTR_COERCE(xLIST_C \<rightarrow> unit) lp)"

definition event_family_key_rep ::
  "'tid scheduler_decode \<Rightarrow> heap_mem \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   'tid set \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow> bool"
where
  "event_family_key_rep D h roots raw_fam abs_fam live K_E \<longleftrightarrow>
     (\<forall>t\<in>live.
        raw_key_at h (event_item_raw_ptr D t) = K_E t) \<and>
     (\<forall>lp\<in>roots. \<forall>t\<in>live.
        Event t \<in> set (ring (abs_fam lp)) \<longrightarrow>
        item_key (abs_fam lp) (Event t) = K_E t)"

definition scheduler_event_root_family_rel ::
  "'tid scheduler_decode \<Rightarrow> heap_mem \<Rightarrow>
   xLIST_C ptr set \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   'tid set \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow> bool"
where
  "scheduler_event_root_family_rel
      D h roots pending raw_fam abs_fam live K_E \<longleftrightarrow>
     scheduler_family_pre_rel h roots raw_fam live D \<and>
     universal_decoder_laws live D \<and>
     pending \<in> roots \<and>
     (\<forall>lp\<in>roots.
        event_family_root_rep D raw_fam abs_fam live lp) \<and>
     event_family_container_rep D h roots raw_fam live \<and>
     event_family_key_rep D h roots raw_fam abs_fam live K_E"

text \<open>Named projections keep downstream proofs independent of the
  conjunction layout of the representation.\<close>

lemma scheduler_event_root_family_relI:
  assumes pre: "scheduler_family_pre_rel h roots raw_fam live D"
    and laws: "universal_decoder_laws live D"
    and pending: "pending \<in> roots"
    and roots:
      "\<And>lp. lp \<in> roots \<Longrightarrow>
        event_family_root_rep D raw_fam abs_fam live lp"
    and containers:
      "event_family_container_rep D h roots raw_fam live"
    and keys:
      "event_family_key_rep D h roots raw_fam abs_fam live K_E"
  shows
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
  using assms by (auto simp: scheduler_event_root_family_rel_def)

lemma scheduler_event_root_family_preD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
  shows "scheduler_family_pre_rel h roots raw_fam live D"
  using rel by (simp add: scheduler_event_root_family_rel_def)

lemma scheduler_event_root_family_decoder_lawsD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
  shows "universal_decoder_laws live D"
  using rel by (simp add: scheduler_event_root_family_rel_def)

lemma scheduler_event_root_family_pending_rootD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
  shows "pending \<in> roots"
  using rel by (simp add: scheduler_event_root_family_rel_def)

lemma scheduler_event_root_family_finite_rootsD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
  shows "finite roots"
  using scheduler_event_root_family_preD[OF rel]
  by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)

lemma scheduler_event_root_family_finite_liveD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
  shows "finite live"
  using scheduler_event_root_family_preD[OF rel]
  by (auto simp: scheduler_family_pre_rel_def universal_tcb_geometry_def)

lemma scheduler_event_root_family_raw_rootD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and root: "lp \<in> roots"
  shows "raw_xlist_rel h lp (raw_fam lp)"
  using scheduler_event_root_family_preD[OF rel] root
  by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)

lemma scheduler_event_root_family_root_repD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and root: "lp \<in> roots"
  shows "event_family_root_rep D raw_fam abs_fam live lp"
  using rel root by (auto simp: scheduler_event_root_family_rel_def)

lemma scheduler_event_root_family_relabelD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and root: "lp \<in> roots"
  shows
    "xlist_relabel (sd_node_decode D) (raw_fam lp) (abs_fam lp)"
  using scheduler_event_root_family_root_repD[OF rel root]
  by (simp add: event_family_root_rep_def)

lemma scheduler_event_root_family_abs_wfD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and root: "lp \<in> roots"
  shows "xlist_wf (abs_fam lp)"
  using scheduler_event_root_family_root_repD[OF rel root]
  by (simp add: event_family_root_rep_def)

lemma scheduler_event_root_family_event_ringD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and root: "lp \<in> roots"
  shows "event_ring (abs_fam lp)"
  using scheduler_event_root_family_root_repD[OF rel root]
  by (simp add: event_family_root_rep_def)

lemma scheduler_event_root_family_raw_nodesD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and root: "lp \<in> roots"
  shows
    "set (ring (raw_fam lp)) \<subseteq> event_item_raw_set live D"
  using scheduler_event_root_family_root_repD[OF rel root]
  by (simp add: event_family_root_rep_def)

lemma scheduler_event_root_family_sched_xlistD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and root: "lp \<in> roots"
  shows "sched_xlist_rel (sd_node_decode D) h lp (abs_fam lp)"
  using scheduler_event_root_family_raw_rootD[OF rel root]
    scheduler_event_root_family_relabelD[OF rel root]
  by (auto simp: sched_xlist_rel_def)

lemma scheduler_event_root_family_event_decodeD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and live: "t \<in> live"
  shows
    "sd_node_decode D (event_item_raw_ptr D t) = Some (Event t)"
  using universal_node_decode_Event_iff[
      OF scheduler_event_root_family_decoder_lawsD[OF rel],
      where p="event_item_raw_ptr D t" and t=t]
    live
  by (simp add: event_item_raw_ptr_def)

text \<open>Physical and abstract membership are pointwise identical for every
  live task and every represented root.\<close>

lemma scheduler_event_root_family_member_iff:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and live: "t \<in> live"
    and root: "lp \<in> roots"
  shows
    "event_item_raw_ptr D t \<in> set (ring (raw_fam lp)) \<longleftrightarrow>
     Event t \<in> set (ring (abs_fam lp))"
proof
  assume raw_member:
    "event_item_raw_ptr D t \<in> set (ring (raw_fam lp))"
  have relabel:
    "xlist_relabel (sd_node_decode D) (raw_fam lp) (abs_fam lp)"
    by (rule scheduler_event_root_family_relabelD[OF rel root])
  obtain n where
      abs_member: "n \<in> set (ring (abs_fam lp))"
    and decode: "sd_node_decode D (event_item_raw_ptr D t) = Some n"
    using xlist_relabel_decoder_left_closed[OF relabel raw_member] by blast
  have event_decode:
    "sd_node_decode D (event_item_raw_ptr D t) = Some (Event t)"
    by (rule scheduler_event_root_family_event_decodeD[OF rel live])
  have "n = Event t"
    using decode event_decode by simp
  then show "Event t \<in> set (ring (abs_fam lp))"
    using abs_member by simp
next
  assume abs_member: "Event t \<in> set (ring (abs_fam lp))"
  have relabel:
    "xlist_relabel (sd_node_decode D) (raw_fam lp) (abs_fam lp)"
    by (rule scheduler_event_root_family_relabelD[OF rel root])
  obtain p where
      raw_member: "p \<in> set (ring (raw_fam lp))"
    and decode: "sd_node_decode D p = Some (Event t)"
    using xlist_relabel_decoder_right_closed[OF relabel abs_member] by blast
  have "p = event_item_raw_ptr D t"
    using universal_node_decode_Event_iff[
        OF scheduler_event_root_family_decoder_lawsD[OF rel],
        where p=p and t=t]
      decode
    by (auto simp: event_item_raw_ptr_def)
  then show
    "event_item_raw_ptr D t \<in> set (ring (raw_fam lp))"
    using raw_member by simp
qed

lemma scheduler_event_root_family_abstract_task_liveD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and root: "lp \<in> roots"
    and member: "Event t \<in> set (ring (abs_fam lp))"
  shows "t \<in> live"
proof -
  have relabel:
    "xlist_relabel (sd_node_decode D) (raw_fam lp) (abs_fam lp)"
    by (rule scheduler_event_root_family_relabelD[OF rel root])
  obtain p where
      decode: "sd_node_decode D p = Some (Event t)"
    using xlist_relabel_decoder_right_closed[OF relabel member] by blast
  show ?thesis
    using universal_node_decode_Event_iff[
      OF scheduler_event_root_family_decoder_lawsD[OF rel],
      where p=p and t=t] decode by blast
qed

text \<open>Per-root count, cursor, topology, and payload destructors.\<close>

lemma scheduler_event_root_family_countD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and root: "lp \<in> roots"
  shows
    "unat (uxNumberOfItems_C (h_val h lp)) =
       length (ring (abs_fam lp))"
proof -
  have raw_count:
    "unat (uxNumberOfItems_C (h_val h lp)) =
       length (ring (raw_fam lp))"
    by (rule raw_xlist_rel_countD[
      OF scheduler_event_root_family_raw_rootD[OF rel root]])
  have lengths:
    "length (ring (raw_fam lp)) = length (ring (abs_fam lp))"
    by (rule xlist_relabel_ring_length[
      OF scheduler_event_root_family_relabelD[OF rel root]])
  show ?thesis using raw_count lengths by simp
qed

lemma scheduler_event_root_family_cursorD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and root: "lp \<in> roots"
  shows
    "rel_option (\<lambda>p n. sd_node_decode D p = Some n)
       (raw_cursor_at h lp) (cursor (abs_fam lp))"
proof -
  have raw_cursor:
    "cursor (raw_fam lp) = raw_cursor_at h lp"
    by (rule raw_xlist_rel_cursorD[
      OF scheduler_event_root_family_raw_rootD[OF rel root]])
  have relabel:
    "xlist_relabel (sd_node_decode D) (raw_fam lp) (abs_fam lp)"
    by (rule scheduler_event_root_family_relabelD[OF rel root])
  from relabel have
    "rel_option (\<lambda>p n. sd_node_decode D p = Some n)
       (cursor (raw_fam lp)) (cursor (abs_fam lp))"
    by (simp add: xlist_relabel_def)
  then show ?thesis using raw_cursor by simp
qed

lemma scheduler_event_root_family_topologyD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and root: "lp \<in> roots"
  shows "raw_ring_links h lp (ring (raw_fam lp))"
  using scheduler_event_root_family_raw_rootD[OF rel root]
  by (simp add: raw_xlist_rel_def raw_xlist_view_def)

lemma scheduler_event_root_family_physical_keyD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and live: "t \<in> live"
  shows "raw_key_at h (event_item_raw_ptr D t) = K_E t"
  using rel live
  by (auto simp: scheduler_event_root_family_rel_def
      event_family_key_rep_def)

lemma scheduler_event_root_family_raw_ring_keyD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and live: "t \<in> live"
    and root: "lp \<in> roots"
    and member:
      "event_item_raw_ptr D t \<in> set (ring (raw_fam lp))"
  shows "item_key (raw_fam lp) (event_item_raw_ptr D t) = K_E t"
proof -
  have payload:
    "item_key (raw_fam lp) (event_item_raw_ptr D t) =
       raw_key_at h (event_item_raw_ptr D t)"
    using raw_xlist_rel_live_itemD[
      OF scheduler_event_root_family_raw_rootD[OF rel root] member]
    by simp
  show ?thesis
    using payload scheduler_event_root_family_physical_keyD[OF rel live]
    by simp
qed

lemma scheduler_event_root_family_abstract_keyD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and live: "t \<in> live"
    and root: "lp \<in> roots"
    and member: "Event t \<in> set (ring (abs_fam lp))"
  shows "item_key (abs_fam lp) (Event t) = K_E t"
  using rel live root member
  by (auto simp: scheduler_event_root_family_rel_def
      event_family_key_rep_def)

text \<open>Exact ownership.  The iff is deliberately explicit: it permits a
  caller to recover membership from pvContainer as well as pvContainer from
  membership, while the NULL theorem characterises the globally unlinked
  case.\<close>

lemma scheduler_event_root_family_container_iff:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and live: "t \<in> live"
    and root: "lp \<in> roots"
  shows
    "event_item_raw_ptr D t \<in> set (ring (raw_fam lp)) \<longleftrightarrow>
     pvContainer_C (h_val h (event_item_raw_ptr D t)) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
  using rel live root
  by (auto simp: scheduler_event_root_family_rel_def
      event_family_container_rep_def)

lemma scheduler_event_root_family_null_iff:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and live: "t \<in> live"
  shows
    "pvContainer_C (h_val h (event_item_raw_ptr D t)) = NULL \<longleftrightarrow>
     raw_family_members roots raw_fam (event_item_raw_ptr D t) = {}"
proof -
  have managed:
    "event_item_raw_ptr D t \<in> event_item_raw_set live D"
    using live by (auto simp: event_item_raw_set_def)
  show ?thesis
    using rel managed
    by (auto simp: scheduler_event_root_family_rel_def
        event_family_container_rep_def
        raw_family_container_faithful_on_def)
qed

lemma scheduler_event_root_family_globally_unlinked_iff:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and live: "t \<in> live"
  shows
    "raw_family_globally_unlinked h roots raw_fam
       (event_item_raw_ptr D t) \<longleftrightarrow>
     raw_family_members roots raw_fam (event_item_raw_ptr D t) = {}"
  using scheduler_event_root_family_null_iff[OF rel live]
  by (auto simp: raw_family_globally_unlinked_def)

lemma scheduler_event_root_family_unlinked_null_iff:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and live: "t \<in> live"
  shows
    "raw_family_globally_unlinked h roots raw_fam
       (event_item_raw_ptr D t) \<longleftrightarrow>
     pvContainer_C (h_val h (event_item_raw_ptr D t)) = NULL"
  using scheduler_event_root_family_null_iff[OF rel live]
  by (auto simp: raw_family_globally_unlinked_def)

lemma scheduler_event_root_family_unique_rootD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and left_root: "lp \<in> roots"
    and right_root: "lq \<in> roots"
    and left_member: "p \<in> set (ring (raw_fam lp))"
    and right_member: "p \<in> set (ring (raw_fam lq))"
  shows "lp = lq"
proof (rule ccontr)
  assume distinct: "lp \<noteq> lq"
  have disjoint:
    "set (ring (raw_fam lp)) \<inter> set (ring (raw_fam lq)) = {}"
    using scheduler_event_root_family_preD[OF rel]
      left_root right_root distinct
    by (auto simp: scheduler_family_pre_rel_def)
  show False using disjoint left_member right_member by blast
qed

lemma scheduler_event_root_family_abstract_unique_rootD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and left_root: "lp \<in> roots"
    and right_root: "lq \<in> roots"
    and left_member: "Event t \<in> set (ring (abs_fam lp))"
    and right_member: "Event t \<in> set (ring (abs_fam lq))"
  shows "lp = lq"
proof -
  have live: "t \<in> live"
    by (rule scheduler_event_root_family_abstract_task_liveD[
      OF rel left_root left_member])
  have left_raw:
    "event_item_raw_ptr D t \<in> set (ring (raw_fam lp))"
    using scheduler_event_root_family_member_iff[OF rel live left_root]
      left_member by simp
  have right_raw:
    "event_item_raw_ptr D t \<in> set (ring (raw_fam lq))"
    using scheduler_event_root_family_member_iff[OF rel live right_root]
      right_member by simp
  show ?thesis
    by (rule scheduler_event_root_family_unique_rootD[
      OF rel left_root right_root left_raw right_raw])
qed

lemma scheduler_event_root_family_member_singletonD:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and root: "lp \<in> roots"
    and member: "p \<in> set (ring (raw_fam lp))"
  shows "raw_family_members roots raw_fam p = {lp}"
proof (rule equalityI)
  show "raw_family_members roots raw_fam p \<subseteq> {lp}"
  proof
    fix lq
    assume lq_member: "lq \<in> raw_family_members roots raw_fam p"
    then have lq_root: "lq \<in> roots"
      and lq_ring: "p \<in> set (ring (raw_fam lq))"
      by (auto simp: raw_family_members_def)
    have "lq = lp"
      by (rule scheduler_event_root_family_unique_rootD[
        OF rel lq_root root lq_ring member])
    then show "lq \<in> {lp}" by simp
  qed
  show "{lp} \<subseteq> raw_family_members roots raw_fam p"
    using root member by (auto simp: raw_family_members_def)
qed

text \<open>The distinguished pending root and all other Event roots induce
  exact physical/abstract task sets; no root or task enumeration is used.\<close>

definition event_family_pending_tasks ::
  "'tid scheduler_decode \<Rightarrow> 'tid set \<Rightarrow>
   xLIST_C ptr \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   'tid set"
where
  "event_family_pending_tasks D live pending raw_fam =
     {t \<in> live.
        event_item_raw_ptr D t \<in> set (ring (raw_fam pending))}"

definition event_family_external_tasks ::
  "'tid scheduler_decode \<Rightarrow> 'tid set \<Rightarrow>
   xLIST_C ptr set \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   'tid set"
where
  "event_family_external_tasks D live roots pending raw_fam =
     {t \<in> live. \<exists>lp\<in>event_external_roots roots pending.
        event_item_raw_ptr D t \<in> set (ring (raw_fam lp))}"

definition event_family_unlinked_tasks ::
  "'tid scheduler_decode \<Rightarrow> 'tid set \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   'tid set"
where
  "event_family_unlinked_tasks D live roots raw_fam =
     {t \<in> live.
        raw_family_members roots raw_fam (event_item_raw_ptr D t) = {}}"

definition event_family_abs_pending_tasks ::
  "xLIST_C ptr \<Rightarrow> (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   'tid set"
where
  "event_family_abs_pending_tasks pending abs_fam =
     event_task_set (abs_fam pending)"

definition event_family_abs_external_tasks ::
  "xLIST_C ptr set \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow> 'tid set"
where
  "event_family_abs_external_tasks roots pending abs_fam =
     {t. \<exists>lp\<in>event_external_roots roots pending.
        Event t \<in> set (ring (abs_fam lp))}"

lemma scheduler_event_root_family_pending_tasks_eq:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
  shows
    "event_family_pending_tasks D live pending raw_fam =
     event_family_abs_pending_tasks pending abs_fam"
proof (rule set_eqI)
  fix t
  show
    "t \<in> event_family_pending_tasks D live pending raw_fam \<longleftrightarrow>
     t \<in> event_family_abs_pending_tasks pending abs_fam"
  proof
    assume raw:
      "t \<in> event_family_pending_tasks D live pending raw_fam"
    then have live: "t \<in> live"
      and member:
        "event_item_raw_ptr D t \<in> set (ring (raw_fam pending))"
      by (auto simp: event_family_pending_tasks_def)
    have root: "pending \<in> roots"
      by (rule scheduler_event_root_family_pending_rootD[OF rel])
    have "Event t \<in> set (ring (abs_fam pending))"
      using scheduler_event_root_family_member_iff[OF rel live root]
        member by simp
    then show
      "t \<in> event_family_abs_pending_tasks pending abs_fam"
      by (simp add: event_family_abs_pending_tasks_def event_task_set_def)
  next
    assume abstract:
      "t \<in> event_family_abs_pending_tasks pending abs_fam"
    then have member: "Event t \<in> set (ring (abs_fam pending))"
      by (simp add: event_family_abs_pending_tasks_def event_task_set_def)
    have root: "pending \<in> roots"
      by (rule scheduler_event_root_family_pending_rootD[OF rel])
    have live: "t \<in> live"
      by (rule scheduler_event_root_family_abstract_task_liveD[
        OF rel root member])
    have raw:
      "event_item_raw_ptr D t \<in> set (ring (raw_fam pending))"
      using scheduler_event_root_family_member_iff[OF rel live root]
        member by simp
    show "t \<in> event_family_pending_tasks D live pending raw_fam"
      using live raw by (simp add: event_family_pending_tasks_def)
  qed
qed

lemma scheduler_event_root_family_external_tasks_eq:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
  shows
    "event_family_external_tasks D live roots pending raw_fam =
     event_family_abs_external_tasks roots pending abs_fam"
proof (rule set_eqI)
  fix t
  show
    "t \<in> event_family_external_tasks D live roots pending raw_fam \<longleftrightarrow>
     t \<in> event_family_abs_external_tasks roots pending abs_fam"
  proof
    assume raw:
      "t \<in> event_family_external_tasks D live roots pending raw_fam"
    then obtain lp where
        live: "t \<in> live"
      and ext: "lp \<in> event_external_roots roots pending"
      and member:
        "event_item_raw_ptr D t \<in> set (ring (raw_fam lp))"
      by (auto simp: event_family_external_tasks_def)
    have root: "lp \<in> roots"
      using ext by (auto simp: event_external_roots_def)
    have abstract: "Event t \<in> set (ring (abs_fam lp))"
      using scheduler_event_root_family_member_iff[OF rel live root]
        member by simp
    show "t \<in> event_family_abs_external_tasks roots pending abs_fam"
      using ext abstract by (auto simp: event_family_abs_external_tasks_def)
  next
    assume abstract:
      "t \<in> event_family_abs_external_tasks roots pending abs_fam"
    then obtain lp where
        ext: "lp \<in> event_external_roots roots pending"
      and member: "Event t \<in> set (ring (abs_fam lp))"
      by (auto simp: event_family_abs_external_tasks_def)
    have root: "lp \<in> roots"
      using ext by (auto simp: event_external_roots_def)
    have live: "t \<in> live"
      by (rule scheduler_event_root_family_abstract_task_liveD[
        OF rel root member])
    have raw:
      "event_item_raw_ptr D t \<in> set (ring (raw_fam lp))"
      using scheduler_event_root_family_member_iff[OF rel live root]
        member by simp
    show "t \<in> event_family_external_tasks D live roots pending raw_fam"
      using live ext raw by (auto simp: event_family_external_tasks_def)
  qed
qed

lemma scheduler_event_root_family_unlinked_tasks_null:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
  shows
    "event_family_unlinked_tasks D live roots raw_fam =
     {t \<in> live.
        pvContainer_C (h_val h (event_item_raw_ptr D t)) = NULL}"
  using scheduler_event_root_family_null_iff[OF rel]
  by (auto simp: event_family_unlinked_tasks_def)

lemma scheduler_event_root_family_live_partition:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
  shows
    "live =
       event_family_pending_tasks D live pending raw_fam \<union>
       event_family_external_tasks D live roots pending raw_fam \<union>
       event_family_unlinked_tasks D live roots raw_fam"
proof (rule set_eqI)
  fix t
  show
    "t \<in> live \<longleftrightarrow>
     t \<in>
       event_family_pending_tasks D live pending raw_fam \<union>
       event_family_external_tasks D live roots pending raw_fam \<union>
       event_family_unlinked_tasks D live roots raw_fam"
  proof
    assume live: "t \<in> live"
    show
      "t \<in>
       event_family_pending_tasks D live pending raw_fam \<union>
       event_family_external_tasks D live roots pending raw_fam \<union>
       event_family_unlinked_tasks D live roots raw_fam"
    proof (cases
        "raw_family_members roots raw_fam (event_item_raw_ptr D t) = {}")
      case True
      then have
        "t \<in> event_family_unlinked_tasks D live roots raw_fam"
        using live by (simp add: event_family_unlinked_tasks_def)
      then show ?thesis by blast
    next
      case False
      then obtain lp where owner:
        "lp \<in> raw_family_members roots raw_fam (event_item_raw_ptr D t)"
        by blast
      then have root: "lp \<in> roots"
        and member:
          "event_item_raw_ptr D t \<in> set (ring (raw_fam lp))"
        by (auto simp: raw_family_members_def)
      show ?thesis
      proof (cases "lp = pending")
        case True
        have
          "t \<in> event_family_pending_tasks D live pending raw_fam"
          using live member True by (simp add: event_family_pending_tasks_def)
        then show ?thesis by blast
      next
        case False
        have ext: "lp \<in> event_external_roots roots pending"
          using root False by (simp add: event_external_roots_def)
        have
          "t \<in> event_family_external_tasks
             D live roots pending raw_fam"
          using live ext member by (auto simp: event_family_external_tasks_def)
        then show ?thesis by blast
      qed
    qed
  next
    assume classified:
      "t \<in>
       event_family_pending_tasks D live pending raw_fam \<union>
       event_family_external_tasks D live roots pending raw_fam \<union>
       event_family_unlinked_tasks D live roots raw_fam"
    then show "t \<in> live"
      by (auto simp: event_family_pending_tasks_def
          event_family_external_tasks_def event_family_unlinked_tasks_def)
  qed
qed

text \<open>
  Frame ledgers for a single target-root removal.  The first states the byte
  obligation for every other Event root; the concrete remove transformer
  discharges it below for arbitrary roots and arbitrary ring shape.  The full
  ledger also names the global live-Event key frame, all nonremoved container
  frames, and the removed NULL result.  Later operation composition can prove
  those clauses independently and then consume them without unfolding heap
  implementation details.
\<close>

definition event_family_non_target_root_frame ::
  "heap_mem \<Rightarrow> heap_mem \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   xLIST_C ptr \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   bool"
where
  "event_family_non_target_root_frame h h' roots target raw_fam \<longleftrightarrow>
     (\<forall>lp\<in>roots - {target}. \<forall>a\<in>raw_xlist_storage lp (raw_fam lp).
        h' a = h a)"

definition event_family_remove_frame_obligations ::
  "'tid scheduler_decode \<Rightarrow> heap_mem \<Rightarrow> heap_mem \<Rightarrow>
   xLIST_C ptr set \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   'tid set \<Rightarrow> 'tid \<Rightarrow> bool"
where
  "event_family_remove_frame_obligations
      D h h' roots target raw_fam live removed \<longleftrightarrow>
     event_family_non_target_root_frame h h' roots target raw_fam \<and>
     (\<forall>t\<in>live.
        raw_key_at h' (event_item_raw_ptr D t) =
          raw_key_at h (event_item_raw_ptr D t)) \<and>
     (\<forall>t\<in>live - {removed}.
        pvContainer_C (h_val h' (event_item_raw_ptr D t)) =
          pvContainer_C (h_val h (event_item_raw_ptr D t))) \<and>
     pvContainer_C (h_val h' (event_item_raw_ptr D removed)) = NULL"

lemma event_family_remove_frame_non_targetD:
  assumes frame:
    "event_family_remove_frame_obligations
       D h h' roots target raw_fam live removed"
  shows "event_family_non_target_root_frame h h' roots target raw_fam"
  using frame by (simp add: event_family_remove_frame_obligations_def)

lemma event_family_remove_frame_keyD:
  assumes frame:
    "event_family_remove_frame_obligations
       D h h' roots target raw_fam live removed"
    and live: "t \<in> live"
  shows
    "raw_key_at h' (event_item_raw_ptr D t) =
     raw_key_at h (event_item_raw_ptr D t)"
  using frame live
  by (auto simp: event_family_remove_frame_obligations_def)

lemma event_family_remove_frame_other_containerD:
  assumes frame:
    "event_family_remove_frame_obligations
       D h h' roots target raw_fam live removed"
    and live: "t \<in> live"
    and other: "t \<noteq> removed"
  shows
    "pvContainer_C (h_val h' (event_item_raw_ptr D t)) =
     pvContainer_C (h_val h (event_item_raw_ptr D t))"
  using frame live other
  by (auto simp: event_family_remove_frame_obligations_def)

lemma event_family_remove_frame_removed_nullD:
  assumes frame:
    "event_family_remove_frame_obligations
       D h h' roots target raw_fam live removed"
  shows
    "pvContainer_C (h_val h' (event_item_raw_ptr D removed)) = NULL"
  using frame by (simp add: event_family_remove_frame_obligations_def)

lemma scheduler_event_root_family_remove_non_target_frame:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and target: "target \<in> roots"
    and member: "p \<in> set (ring (raw_fam target))"
  shows
    "event_family_non_target_root_frame h
       (raw_remove_concrete_heap h p) roots target raw_fam"
  unfolding event_family_non_target_root_frame_def
proof (intro ballI)
  fix other
  assume other: "other \<in> roots - {target}"
  fix a
  assume address: "a \<in> raw_xlist_storage other (raw_fam other)"
  have other_root: "other \<in> roots" and distinct: "target \<noteq> other"
    using other by auto
  show "raw_remove_concrete_heap h p a = h a"
    by (rule raw_remove_family_non_target_byte_frame[
      OF scheduler_event_root_family_preD[OF rel]
         target other_root distinct member address])
qed

lemma scheduler_event_root_family_remove_item_effect:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and root: "lp \<in> roots"
    and live: "t \<in> live"
    and member:
      "event_item_raw_ptr D t \<in> set (ring (raw_fam lp))"
  shows
    "raw_key_at (raw_remove_concrete_heap h (event_item_raw_ptr D t))
       (event_item_raw_ptr D t) = K_E t \<and>
     pvContainer_C
       (h_val (raw_remove_concrete_heap h (event_item_raw_ptr D t))
         (event_item_raw_ptr D t)) = NULL"
proof -
  have raw: "raw_xlist_rel h lp (raw_fam lp)"
    by (rule scheduler_event_root_family_raw_rootD[OF rel root])
  have key_frame:
    "raw_key_at (raw_remove_concrete_heap h (event_item_raw_ptr D t))
       (event_item_raw_ptr D t) =
     raw_key_at h (event_item_raw_ptr D t)"
    by (rule raw_remove_concrete_heap_preserves_item_key[OF raw member])
  have removed:
    "pvContainer_C
       (h_val (raw_remove_concrete_heap h (event_item_raw_ptr D t))
         (event_item_raw_ptr D t)) = NULL"
    using raw_remove_concrete_heap_removed_item_effect[OF raw member] by blast
  show ?thesis
    using key_frame removed
      scheduler_event_root_family_physical_keyD[OF rel live]
    by simp
qed

lemma scheduler_event_root_family_event_item_ptr_inj:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and left_live: "u \<in> live"
    and right_live: "t \<in> live"
    and equal: "event_item_raw_ptr D u = event_item_raw_ptr D t"
  shows "u = t"
proof -
  have decode_u:
    "sd_node_decode D (event_item_raw_ptr D u) = Some (Event u)"
    by (rule scheduler_event_root_family_event_decodeD[OF rel left_live])
  have decode_t:
    "sd_node_decode D (event_item_raw_ptr D t) = Some (Event t)"
    by (rule scheduler_event_root_family_event_decodeD[OF rel right_live])
  have some_eq: "Some (Event u) = Some (Event t)"
    using decode_u decode_t equal by (simp only: equal)
  have event_eq: "Event u = Event t"
    using some_eq by (simp only: option.inject)
  show ?thesis using event_eq by (simp only: node_kind.inject)
qed

lemma scheduler_event_remove_remaining_payloadD:
  assumes raw: "raw_xlist_rel h lp xs"
    and removed: "p \<in> set (ring xs)"
    and remaining: "q \<in> set (remove1 p (ring xs))"
  shows
    "raw_key_at (raw_remove_concrete_heap h p) q = raw_key_at h q \<and>
     pvContainer_C (h_val (raw_remove_concrete_heap h p) q) =
       pvContainer_C (h_val h q)"
proof -
  note payload_all =
    raw_remove_concrete_heap_payload_effect[OF raw removed]
  show ?thesis by (rule bspec[OF payload_all remaining])
qed

lemma scheduler_event_root_family_remove_remaining_payload_frame:
  assumes rel:
    "scheduler_event_root_family_rel
       D h roots pending raw_fam abs_fam live K_E"
    and root: "lp \<in> roots"
    and removed_live: "t \<in> live"
    and remaining_live: "u \<in> live"
    and different: "u \<noteq> t"
    and removed_member:
      "event_item_raw_ptr D t \<in> set (ring (raw_fam lp))"
    and remaining_member:
      "event_item_raw_ptr D u \<in> set (ring (raw_fam lp))"
  shows
    "raw_key_at (raw_remove_concrete_heap h (event_item_raw_ptr D t))
       (event_item_raw_ptr D u) = K_E u \<and>
     pvContainer_C
       (h_val (raw_remove_concrete_heap h (event_item_raw_ptr D t))
         (event_item_raw_ptr D u)) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
proof -
  have raw: "raw_xlist_rel h lp (raw_fam lp)"
    by (rule scheduler_event_root_family_raw_rootD[OF rel root])
  have pointer_different:
    "event_item_raw_ptr D u \<noteq> event_item_raw_ptr D t"
  proof
    assume equal:
      "event_item_raw_ptr D u = event_item_raw_ptr D t"
    have same: "u = t"
      by (rule scheduler_event_root_family_event_item_ptr_inj[
            OF rel remaining_live removed_live equal])
    show False using different same by contradiction
  qed
  have remaining_after_remove:
    "event_item_raw_ptr D u \<in>
       set (remove1 (event_item_raw_ptr D t) (ring (raw_fam lp)))"
    using remaining_member
    by (simp only: in_set_remove1[OF pointer_different])
  have payload:
    "raw_key_at (raw_remove_concrete_heap h (event_item_raw_ptr D t))
       (event_item_raw_ptr D u) =
       raw_key_at h (event_item_raw_ptr D u) \<and>
     pvContainer_C
       (h_val (raw_remove_concrete_heap h (event_item_raw_ptr D t))
         (event_item_raw_ptr D u)) =
       pvContainer_C (h_val h (event_item_raw_ptr D u))"
  proof -
    show ?thesis
      by (rule scheduler_event_remove_remaining_payloadD[
            OF raw removed_member remaining_after_remove])
  qed
  have old_container:
    "pvContainer_C (h_val h (event_item_raw_ptr D u)) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
  proof -
    have container_iff:
      "event_item_raw_ptr D u \<in> set (ring (raw_fam lp)) \<longleftrightarrow>
       pvContainer_C (h_val h (event_item_raw_ptr D u)) =
         PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
      by (rule scheduler_event_root_family_container_iff[
            OF rel remaining_live root])
    show ?thesis by (rule iffD1[OF container_iff remaining_member])
  qed
  have old_key:
    "raw_key_at h (event_item_raw_ptr D u) = K_E u"
    by (rule scheduler_event_root_family_physical_keyD[OF rel remaining_live])
  have new_key:
    "raw_key_at (raw_remove_concrete_heap h (event_item_raw_ptr D t))
       (event_item_raw_ptr D u) = K_E u"
  proof -
    have frame:
      "raw_key_at (raw_remove_concrete_heap h (event_item_raw_ptr D t))
         (event_item_raw_ptr D u) =
       raw_key_at h (event_item_raw_ptr D u)"
      by (rule payload[THEN conjunct1])
    show ?thesis by (rule trans[OF frame old_key])
  qed
  have new_container:
    "pvContainer_C
       (h_val (raw_remove_concrete_heap h (event_item_raw_ptr D t))
         (event_item_raw_ptr D u)) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
  proof -
    have frame:
      "pvContainer_C
         (h_val (raw_remove_concrete_heap h (event_item_raw_ptr D t))
           (event_item_raw_ptr D u)) =
       pvContainer_C (h_val h (event_item_raw_ptr D u))"
      by (rule payload[THEN conjunct2])
    show ?thesis by (rule trans[OF frame old_container])
  qed
  show ?thesis by (rule conjI[OF new_key new_container])
qed

end
