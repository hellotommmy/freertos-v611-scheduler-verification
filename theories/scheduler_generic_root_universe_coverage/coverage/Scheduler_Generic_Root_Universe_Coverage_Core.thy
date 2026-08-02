theory Scheduler_Generic_Root_Universe_Coverage_Core
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Universe_Base.Scheduler_Generic_Root_Universe_Base"
begin

text \<open>
  Total Generic-item observations.  K_G is intentionally total on live tasks:
  a Generic item may be temporarily unlinked, but its physical xItemValue
  remains observable and must not be guessed from its current root role.

  Here live is the allocated-and-observable TCB domain of this family
  relation.  In particular, a TCB still owned by xTasksWaitingTermination must
  remain in this domain until its memory is reclaimed.  A later whole-
  scheduler relation must not identify this domain with the runnable-task
  count without a separate lifecycle theorem.
\<close>

definition generic_item_raw_ptr ::
  "'tid scheduler_decode \<Rightarrow> 'tid \<Rightarrow> raw_node_id"
where
  "generic_item_raw_ptr D t =
     abi_generic_list_item_ptr (sd_tcb_ptr D t)"

definition generic_item_raw_set ::
  "'tid set \<Rightarrow> 'tid scheduler_decode \<Rightarrow> raw_node_id set"
where
  "generic_item_raw_set live D = generic_item_raw_ptr D ` live"

definition generic_family_root_rep ::
  "'tid scheduler_decode \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   'tid set \<Rightarrow> xLIST_C ptr \<Rightarrow> bool"
where
  "generic_family_root_rep D raw_fam abs_fam live lp \<longleftrightarrow>
     set (ring (raw_fam lp)) \<subseteq> generic_item_raw_set live D \<and>
     xlist_relabel (sd_node_decode D) (raw_fam lp) (abs_fam lp) \<and>
     xlist_wf (abs_fam lp) \<and>
     generic_ring (abs_fam lp)"

definition generic_family_container_rep ::
  "'tid scheduler_decode \<Rightarrow> heap_mem \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   'tid set \<Rightarrow> bool"
where
  "generic_family_container_rep D h roots raw_fam live \<longleftrightarrow>
     raw_family_container_faithful_on h roots raw_fam
       (generic_item_raw_set live D) \<and>
     (\<forall>t\<in>live. \<forall>lp\<in>roots.
        generic_item_raw_ptr D t \<in> set (ring (raw_fam lp)) \<longleftrightarrow>
        pvContainer_C (h_val h (generic_item_raw_ptr D t)) =
          PTR_COERCE(xLIST_C \<rightarrow> unit) lp)"

definition generic_family_key_rep ::
  "'tid scheduler_decode \<Rightarrow> heap_mem \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   'tid set \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow> bool"
where
  "generic_family_key_rep D h roots raw_fam abs_fam live K_G \<longleftrightarrow>
     (\<forall>t\<in>live.
        raw_key_at h (generic_item_raw_ptr D t) = K_G t) \<and>
     (\<forall>lp\<in>roots. \<forall>t\<in>live.
        Generic t \<in> set (ring (abs_fam lp)) \<longrightarrow>
        item_key (abs_fam lp) (Generic t) = K_G t)"

definition GenericRootFamilyCoverage ::
  "'tid scheduler_decode \<Rightarrow> heap_mem \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   'tid set \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow> bool"
where
  "GenericRootFamilyCoverage
      D h roots raw_fam abs_fam live K_G \<longleftrightarrow>
     roots = GenericRootUniverse \<and>
     scheduler_family_pre_rel h roots raw_fam live D \<and>
     universal_decoder_laws live D \<and>
     (\<forall>lp\<in>roots.
        generic_family_root_rep D raw_fam abs_fam live lp) \<and>
     generic_family_container_rep D h roots raw_fam live \<and>
     generic_family_key_rep D h roots raw_fam abs_fam live K_G"

lemma GenericRootFamilyCoverageI:
  assumes universe: "roots = GenericRootUniverse"
    and pre: "scheduler_family_pre_rel h roots raw_fam live D"
    and laws: "universal_decoder_laws live D"
    and root_rep:
      "\<And>lp. lp \<in> roots \<Longrightarrow>
        generic_family_root_rep D raw_fam abs_fam live lp"
    and containers:
      "generic_family_container_rep D h roots raw_fam live"
    and keys:
      "generic_family_key_rep D h roots raw_fam abs_fam live K_G"
  shows
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
  using assms by (auto simp: GenericRootFamilyCoverage_def)

lemma GenericRootFamilyCoverage_universeD:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
  shows "roots = GenericRootUniverse"
  using cov by (simp add: GenericRootFamilyCoverage_def)

lemma GenericRootFamilyCoverage_preD:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
  shows "scheduler_family_pre_rel h roots raw_fam live D"
  using cov unfolding GenericRootFamilyCoverage_def by blast

lemma GenericRootFamilyCoverage_decoder_lawsD:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
  shows "universal_decoder_laws live D"
  using cov unfolding GenericRootFamilyCoverage_def by blast

lemma GenericRootFamilyCoverage_container_repD:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
  shows "generic_family_container_rep D h roots raw_fam live"
  using cov unfolding GenericRootFamilyCoverage_def by blast

lemma GenericRootFamilyCoverage_key_repD:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
  shows "generic_family_key_rep D h roots raw_fam abs_fam live K_G"
  using cov unfolding GenericRootFamilyCoverage_def by blast

lemma GenericRootFamilyCoverage_finite_rootsD:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
  shows "finite roots"
  using GenericRootFamilyCoverage_universeD[OF cov] by simp

lemma GenericRootFamilyCoverage_finite_liveD:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
  shows "finite live"
proof -
  have geometry: "universal_tcb_geometry live D"
    using GenericRootFamilyCoverage_preD[OF cov]
    by (simp add: scheduler_family_pre_rel_def)
  show "finite live"
    by (rule universal_tcb_geometry_finiteD[OF geometry])
qed

lemma GenericRootFamilyCoverage_raw_rootD:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
    and root: "lp \<in> roots"
  shows "raw_xlist_rel h lp (raw_fam lp)"
  using GenericRootFamilyCoverage_preD[OF cov] root
  by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)

lemma GenericRootFamilyCoverage_root_repD:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
    and root: "lp \<in> roots"
  shows "generic_family_root_rep D raw_fam abs_fam live lp"
  using cov root by (auto simp: GenericRootFamilyCoverage_def)

lemma GenericRootFamilyCoverage_relabelD:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
    and root: "lp \<in> roots"
  shows
    "xlist_relabel (sd_node_decode D) (raw_fam lp) (abs_fam lp)"
  using GenericRootFamilyCoverage_root_repD[OF cov root]
  by (simp add: generic_family_root_rep_def)

lemma GenericRootFamilyCoverage_generic_ringD:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
    and root: "lp \<in> roots"
  shows "generic_ring (abs_fam lp)"
  using GenericRootFamilyCoverage_root_repD[OF cov root]
  by (simp add: generic_family_root_rep_def)

lemma GenericRootFamilyCoverage_root_live_tcb_disjointD:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
    and root: "lp \<in> roots"
    and task: "t \<in> live"
  shows
    "raw_list_region lp \<inter>
       universal_tcb_region (sd_tcb_ptr D t) = {}"
  using GenericRootFamilyCoverage_preD[OF cov] root task
  by (auto simp: scheduler_family_pre_rel_def)

lemma GenericRootFamilyCoverage_physical_keyD:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
    and task: "t \<in> live"
  shows "raw_key_at h (generic_item_raw_ptr D t) = K_G t"
  using GenericRootFamilyCoverage_key_repD[OF cov] task
  by (auto simp: generic_family_key_rep_def)

lemma GenericRootFamilyCoverage_abstract_keyD:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
    and task: "t \<in> live"
    and root: "lp \<in> roots"
    and member: "Generic t \<in> set (ring (abs_fam lp))"
  shows "item_key (abs_fam lp) (Generic t) = K_G t"
  using GenericRootFamilyCoverage_key_repD[OF cov]
    task root member
  by (auto simp: generic_family_key_rep_def)

lemma GenericRootFamilyCoverage_generic_decodeD:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
    and task: "t \<in> live"
  shows
    "sd_node_decode D (generic_item_raw_ptr D t) = Some (Generic t)"
  using universal_node_decode_Generic_iff[
      OF GenericRootFamilyCoverage_decoder_lawsD[OF cov],
      where p="generic_item_raw_ptr D t" and t=t]
    task
  by (simp add: generic_item_raw_ptr_def)

lemma GenericRootFamilyCoverage_member_iff:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
    and task: "t \<in> live"
    and root: "lp \<in> roots"
  shows
    "generic_item_raw_ptr D t \<in> set (ring (raw_fam lp)) \<longleftrightarrow>
     Generic t \<in> set (ring (abs_fam lp))"
proof
  assume raw_member:
    "generic_item_raw_ptr D t \<in> set (ring (raw_fam lp))"
  obtain n where
      abs_member: "n \<in> set (ring (abs_fam lp))"
    and decode: "sd_node_decode D (generic_item_raw_ptr D t) = Some n"
    using xlist_relabel_decoder_left_closed[
      OF GenericRootFamilyCoverage_relabelD[OF cov root] raw_member]
    by blast
  have expected:
    "sd_node_decode D (generic_item_raw_ptr D t) = Some (Generic t)"
    by (rule GenericRootFamilyCoverage_generic_decodeD[OF cov task])
  show "Generic t \<in> set (ring (abs_fam lp))"
    using abs_member decode expected by simp
next
  assume abs_member: "Generic t \<in> set (ring (abs_fam lp))"
  obtain p where
      raw_member: "p \<in> set (ring (raw_fam lp))"
    and decode: "sd_node_decode D p = Some (Generic t)"
    using xlist_relabel_decoder_right_closed[
      OF GenericRootFamilyCoverage_relabelD[OF cov root] abs_member]
    by blast
  have "p = generic_item_raw_ptr D t"
    using universal_node_decode_Generic_iff[
      OF GenericRootFamilyCoverage_decoder_lawsD[OF cov],
      where p=p and t=t] decode
    by (auto simp: generic_item_raw_ptr_def)
  then show
    "generic_item_raw_ptr D t \<in> set (ring (raw_fam lp))"
    using raw_member by simp
qed

lemma GenericRootFamilyCoverage_container_iff:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
    and task: "t \<in> live"
    and root: "lp \<in> roots"
  shows
    "generic_item_raw_ptr D t \<in> set (ring (raw_fam lp)) \<longleftrightarrow>
     pvContainer_C (h_val h (generic_item_raw_ptr D t)) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
  using GenericRootFamilyCoverage_container_repD[OF cov]
    task root
  by (auto simp: generic_family_container_rep_def)

lemma GenericRootFamilyCoverage_abstract_container_iff:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
    and task: "t \<in> live"
    and root: "lp \<in> roots"
  shows
    "Generic t \<in> set (ring (abs_fam lp)) \<longleftrightarrow>
     pvContainer_C (h_val h (generic_item_raw_ptr D t)) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
  using GenericRootFamilyCoverage_member_iff[OF cov task root]
    GenericRootFamilyCoverage_container_iff[OF cov task root]
  by blast

lemma GenericRootFamilyCoverage_null_iff_global_absence:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
    and task: "t \<in> live"
  shows
    "pvContainer_C (h_val h (generic_item_raw_ptr D t)) = NULL \<longleftrightarrow>
     raw_family_members roots raw_fam (generic_item_raw_ptr D t) = {}"
proof -
  have managed:
    "generic_item_raw_ptr D t \<in> generic_item_raw_set live D"
    using task by (auto simp: generic_item_raw_set_def)
  show ?thesis
    using GenericRootFamilyCoverage_container_repD[OF cov] managed
    by (auto simp: generic_family_container_rep_def
        raw_family_container_faithful_on_def)
qed

lemma GenericRootFamilyCoverage_unique_rootD:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
    and left_root: "lp \<in> roots"
    and right_root: "lq \<in> roots"
    and left_member: "p \<in> set (ring (raw_fam lp))"
    and right_member: "p \<in> set (ring (raw_fam lq))"
  shows "lp = lq"
proof (rule ccontr)
  assume different: "lp \<noteq> lq"
  have disjoint:
    "set (ring (raw_fam lp)) \<inter> set (ring (raw_fam lq)) = {}"
    using GenericRootFamilyCoverage_preD[OF cov]
      left_root right_root different
    by (auto simp: scheduler_family_pre_rel_def)
  show False using disjoint left_member right_member by blast
qed

lemma GenericRootFamilyCoverage_nonnull_iff_unique_root:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
    and task: "t \<in> live"
  shows
    "pvContainer_C (h_val h (generic_item_raw_ptr D t)) \<noteq> NULL
       \<longleftrightarrow>
     (\<exists>!lp. lp \<in> roots \<and>
        generic_item_raw_ptr D t \<in> set (ring (raw_fam lp)))"
proof
  assume nonnull:
    "pvContainer_C (h_val h (generic_item_raw_ptr D t)) \<noteq> NULL"
  have nonempty:
    "raw_family_members roots raw_fam (generic_item_raw_ptr D t) \<noteq> {}"
    using GenericRootFamilyCoverage_null_iff_global_absence[OF cov task]
      nonnull by blast
  then obtain lp where owner:
    "lp \<in> raw_family_members roots raw_fam (generic_item_raw_ptr D t)"
    by blast
  then have root: "lp \<in> roots"
    and member:
      "generic_item_raw_ptr D t \<in> set (ring (raw_fam lp))"
    by (auto simp: raw_family_members_def)
  show
    "\<exists>!lp. lp \<in> roots \<and>
       generic_item_raw_ptr D t \<in> set (ring (raw_fam lp))"
  proof (rule ex1I[where a=lp])
    show
      "lp \<in> roots \<and>
       generic_item_raw_ptr D t \<in> set (ring (raw_fam lp))"
      using root member by blast
    fix lq
    assume candidate:
      "lq \<in> roots \<and>
       generic_item_raw_ptr D t \<in> set (ring (raw_fam lq))"
    show "lq = lp"
      by (rule GenericRootFamilyCoverage_unique_rootD[
          OF cov candidate[THEN conjunct1] root
             candidate[THEN conjunct2] member])
  qed
next
  assume unique:
    "\<exists>!lp. lp \<in> roots \<and>
       generic_item_raw_ptr D t \<in> set (ring (raw_fam lp))"
  then obtain lp where root: "lp \<in> roots"
    and member:
      "generic_item_raw_ptr D t \<in> set (ring (raw_fam lp))"
    by blast
  have nonempty:
    "raw_family_members roots raw_fam (generic_item_raw_ptr D t) \<noteq> {}"
    using root member by (auto simp: raw_family_members_def)
  show
    "pvContainer_C (h_val h (generic_item_raw_ptr D t)) \<noteq> NULL"
    using GenericRootFamilyCoverage_null_iff_global_absence[OF cov task]
      nonempty by blast
qed

text \<open>
  The following destructor is the explicit counterexample exclusion: a state
  satisfying GenericRootFamilyCoverage cannot silently omit a ready slot or
  xTasksWaitingTermination.  It also cannot reclassify pending as Generic.
\<close>

theorem GenericRootFamilyCoverage_no_configured_root_omission:
  assumes cov:
    "GenericRootFamilyCoverage
       D h roots raw_fam abs_fam live K_G"
  shows
    "(\<forall>p<4.
       abi_list_ptr (sr_ready generated_scheduler_roots p) \<in> roots) \<and>
     abi_list_ptr (sr_delayed_a generated_scheduler_roots) \<in> roots \<and>
     abi_list_ptr (sr_delayed_b generated_scheduler_roots) \<in> roots \<and>
     abi_list_ptr (sr_suspended generated_scheduler_roots) \<in> roots \<and>
     abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_' \<in> roots \<and>
     GeneratedPendingEventRoot \<notin> roots"
proof -
  have universe: "roots = GenericRootUniverse"
    by (rule GenericRootFamilyCoverage_universeD[OF cov])
  have ready:
    "\<forall>p<4.
       abi_list_ptr (sr_ready generated_scheduler_roots p) \<in> roots"
  proof (intro allI impI)
    fix p :: nat
    assume bound: "p < 4"
    have
      "abi_list_ptr (sr_ready generated_scheduler_roots p)
         \<in> GenericRootUniverse"
      by (rule GenericRootUniverse_readyI[OF bound])
    then show
      "abi_list_ptr (sr_ready generated_scheduler_roots p) \<in> roots"
      using universe by simp
  qed
  have delayed_a:
    "abi_list_ptr (sr_delayed_a generated_scheduler_roots) \<in> roots"
    using universe GenericRootUniverse_delayed_aI by blast
  have delayed_b:
    "abi_list_ptr (sr_delayed_b generated_scheduler_roots) \<in> roots"
    using universe GenericRootUniverse_delayed_bI by blast
  have suspended:
    "abi_list_ptr (sr_suspended generated_scheduler_roots) \<in> roots"
    using universe GenericRootUniverse_suspendedI by blast
  have termination_root:
    "abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_' \<in> roots"
    using universe GenericRootUniverse_terminationI by blast
  have pending: "GeneratedPendingEventRoot \<notin> roots"
    using universe GeneratedPendingEventRoot_not_Generic by blast
  show ?thesis
    using ready delayed_a delayed_b suspended termination_root pending by blast
qed

text \<open>
  Event roots are different: pending is the one static scheduler Event root,
  while application queue/semaphore/event-group roots are runtime objects.
  The arbitrary finite set external is supplied by the legal input state.
  EventExternalRootInputWF is the explicit allocation/geometry obligation on
  those runtime objects; no external address or population is fixed here.
\<close>

definition EventRootUniverse ::
  "xLIST_C ptr set \<Rightarrow> xLIST_C ptr set"
where
  "EventRootUniverse external = insert GeneratedPendingEventRoot external"

definition EventExternalRootInputWF :: "xLIST_C ptr set \<Rightarrow> bool"
where
  "EventExternalRootInputWF external \<longleftrightarrow>
     finite external \<and>
     GeneratedPendingEventRoot \<notin> external \<and>
     external \<inter> GenericRootUniverse = {} \<and>
     (\<forall>lp\<in>EventRootUniverse external. c_guard lp) \<and>
     (\<forall>lp\<in>EventRootUniverse external.
      \<forall>lq\<in>EventRootUniverse external.
        lp \<noteq> lq \<longrightarrow>
          raw_list_region lp \<inter> raw_list_region lq = {}) \<and>
     (\<forall>lp\<in>EventRootUniverse external.
      \<forall>g\<in>GenericRootUniverse.
        raw_list_region lp \<inter> raw_list_region g = {})"

definition EventRootFamilyCoverage ::
  "xLIST_C ptr set \<Rightarrow> 'tid scheduler_decode \<Rightarrow>
   heap_mem \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   'tid set \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow> bool"
where
  "EventRootFamilyCoverage
      external D h raw_fam abs_fam live K_E \<longleftrightarrow>
     EventExternalRootInputWF external \<and>
     scheduler_event_root_family_rel D h
       (EventRootUniverse external) GeneratedPendingEventRoot
       raw_fam abs_fam live K_E"

lemma EventRootUniverse_finite:
  assumes "EventExternalRootInputWF external"
  shows "finite (EventRootUniverse external)"
  using assms by (simp add: EventExternalRootInputWF_def EventRootUniverse_def)

lemma EventRootUniverse_pendingI [simp]:
  "GeneratedPendingEventRoot \<in> EventRootUniverse external"
  by (simp add: EventRootUniverse_def)

lemma EventRootUniverse_externalI:
  assumes "lp \<in> external"
  shows "lp \<in> EventRootUniverse external"
  using assms by (simp add: EventRootUniverse_def)

lemma EventRootFamilyCoverage_relD:
  assumes cov:
    "EventRootFamilyCoverage
       external D h raw_fam abs_fam live K_E"
  shows
    "scheduler_event_root_family_rel D h
       (EventRootUniverse external) GeneratedPendingEventRoot
       raw_fam abs_fam live K_E"
  using cov by (simp add: EventRootFamilyCoverage_def)

lemma EventRootFamilyCoverage_external_wfD:
  assumes cov:
    "EventRootFamilyCoverage
       external D h raw_fam abs_fam live K_E"
  shows "EventExternalRootInputWF external"
  using cov by (simp add: EventRootFamilyCoverage_def)

lemma EventRootFamilyCoverage_null_iff_global_absence:
  assumes cov:
    "EventRootFamilyCoverage
       external D h raw_fam abs_fam live K_E"
    and task: "t \<in> live"
  shows
    "pvContainer_C (h_val h (event_item_raw_ptr D t)) = NULL \<longleftrightarrow>
     raw_family_members (EventRootUniverse external) raw_fam
       (event_item_raw_ptr D t) = {}"
  by (rule scheduler_event_root_family_null_iff[
      OF EventRootFamilyCoverage_relD[OF cov] task])

lemma EventRootFamilyCoverage_relabelD:
  assumes cov:
    "EventRootFamilyCoverage
       external D h raw_fam abs_fam live K_E"
    and root: "lp \<in> EventRootUniverse external"
  shows
    "xlist_relabel (sd_node_decode D) (raw_fam lp) (abs_fam lp)"
  by (rule scheduler_event_root_family_relabelD[
      OF EventRootFamilyCoverage_relD[OF cov] root])

lemma EventRootFamilyCoverage_container_iff:
  assumes cov:
    "EventRootFamilyCoverage
       external D h raw_fam abs_fam live K_E"
    and task: "t \<in> live"
    and root: "lp \<in> EventRootUniverse external"
  shows
    "event_item_raw_ptr D t \<in> set (ring (raw_fam lp)) \<longleftrightarrow>
     pvContainer_C (h_val h (event_item_raw_ptr D t)) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
  by (rule scheduler_event_root_family_container_iff[
      OF EventRootFamilyCoverage_relD[OF cov] task root])

lemma EventRootFamilyCoverage_abstract_container_iff:
  assumes cov:
    "EventRootFamilyCoverage
       external D h raw_fam abs_fam live K_E"
    and task: "t \<in> live"
    and root: "lp \<in> EventRootUniverse external"
  shows
    "Event t \<in> set (ring (abs_fam lp)) \<longleftrightarrow>
     pvContainer_C (h_val h (event_item_raw_ptr D t)) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
  using scheduler_event_root_family_member_iff[
      OF EventRootFamilyCoverage_relD[OF cov] task root]
    EventRootFamilyCoverage_container_iff[OF cov task root]
  by blast

lemma EventRootFamilyCoverage_physical_keyD:
  assumes cov:
    "EventRootFamilyCoverage
       external D h raw_fam abs_fam live K_E"
    and task: "t \<in> live"
  shows "raw_key_at h (event_item_raw_ptr D t) = K_E t"
  by (rule scheduler_event_root_family_physical_keyD[
      OF EventRootFamilyCoverage_relD[OF cov] task])

lemma EventRootFamilyCoverage_generic_roots_disjointD:
  assumes cov:
    "EventRootFamilyCoverage
       external D h raw_fam abs_fam live K_E"
  shows
    "EventRootUniverse external \<inter> GenericRootUniverse = {}"
proof -
  have wf: "EventExternalRootInputWF external"
    by (rule EventRootFamilyCoverage_external_wfD[OF cov])
  have external_disjoint:
    "external \<inter> GenericRootUniverse = {}"
    using wf by (simp add: EventExternalRootInputWF_def)
  show ?thesis
    using external_disjoint
    by (auto simp: EventRootUniverse_def)
qed

lemma EventRootFamilyCoverage_nonnull_unique_root:
  assumes cov:
    "EventRootFamilyCoverage
       external D h raw_fam abs_fam live K_E"
    and task: "t \<in> live"
    and nonnull:
      "pvContainer_C (h_val h (event_item_raw_ptr D t)) \<noteq> NULL"
  shows
    "\<exists>!lp. lp \<in> EventRootUniverse external \<and>
       event_item_raw_ptr D t \<in> set (ring (raw_fam lp))"
proof -
  note rel = EventRootFamilyCoverage_relD[OF cov]
  have nonempty:
    "raw_family_members (EventRootUniverse external) raw_fam
       (event_item_raw_ptr D t) \<noteq> {}"
    using EventRootFamilyCoverage_null_iff_global_absence[OF cov task]
      nonnull by blast
  then obtain lp where owner:
    "lp \<in> raw_family_members (EventRootUniverse external) raw_fam
       (event_item_raw_ptr D t)"
    by blast
  then have root: "lp \<in> EventRootUniverse external"
    and member:
      "event_item_raw_ptr D t \<in> set (ring (raw_fam lp))"
    by (auto simp: raw_family_members_def)
  show ?thesis
  proof (rule ex1I[where a=lp])
    show
      "lp \<in> EventRootUniverse external \<and>
       event_item_raw_ptr D t \<in> set (ring (raw_fam lp))"
      using root member by blast
    fix lq
    assume candidate:
      "lq \<in> EventRootUniverse external \<and>
       event_item_raw_ptr D t \<in> set (ring (raw_fam lq))"
    show "lq = lp"
      by (rule scheduler_event_root_family_unique_rootD[
          OF rel candidate[THEN conjunct1] root
             candidate[THEN conjunct2] member])
  qed
qed

lemma EventRootFamilyCoverage_event_generic_classification:
  assumes cov:
    "EventRootFamilyCoverage
       external D h raw_fam abs_fam live K_E"
  shows
    "GeneratedPendingEventRoot \<in> EventRootUniverse external \<and>
     abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_'
       \<notin> EventRootUniverse external"
proof -
  have disjoint:
    "EventRootUniverse external \<inter> GenericRootUniverse = {}"
    by (rule EventRootFamilyCoverage_generic_roots_disjointD[OF cov])
  have pending:
    "GeneratedPendingEventRoot \<in> EventRootUniverse external"
    by simp
  have termination_root:
    "abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_'
       \<in> GenericRootUniverse"
    by simp
  have
    "abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_'
       \<notin> EventRootUniverse external"
    using disjoint termination_root by blast
  then show ?thesis using pending by blast
qed

text \<open>
  Boundary statement.  This theory closes only the universe-coverage hole:
  Generic roots are complete for this frozen build and Event roots are
  complete relative to the explicitly supplied legal external-root family.
  It does not yet prove preservation of either coverage relation through the
  whole generated tick/delay/resume bodies.
\<close>

end
