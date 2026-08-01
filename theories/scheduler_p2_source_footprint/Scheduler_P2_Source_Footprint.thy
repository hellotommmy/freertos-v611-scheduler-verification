theory Scheduler_P2_Source_Footprint
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Raw_Relation.Scheduler_P2_Raw_Relation"
    "EAL6_FreeRTOS_V611_Scheduler_List_ABI_Read_Lenses.Scheduler_List_ABI_Read_Lenses"
    "EAL6_FreeRTOS_V611_List_Raw_R6_Ordered_Insert_Empty_Source.List_V611_Raw_R6_Ordered_Insert_Empty_Source"
begin

text \<open>
  The P2 source footprint is an explicit source-facing assumption package.
  It is deliberately stronger than the list representation relation: list
  shape alone does not establish guards or separation for scheduler globals,
  TCB objects, embedded items, or the eight physical list roots.
\<close>

definition scheduler_generic_item_ptr ::
  "Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   Scheduler_V611_Parse.xLIST_ITEM_C ptr"
where
  "scheduler_generic_item_ptr tp =
    PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
      &(tp\<rightarrow>[''xGenericListItem_C''])"

definition scheduler_event_item_ptr ::
  "Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   Scheduler_V611_Parse.xLIST_ITEM_C ptr"
where
  "scheduler_event_item_ptr tp =
    PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
      &(tp\<rightarrow>[''xEventListItem_C''])"

lemma scheduler_generic_item_ptr_ptr_val [simp]:
  "ptr_val (scheduler_generic_item_ptr tp) = ptr_val tp + 4"
  by (simp add: scheduler_generic_item_ptr_def field_lvalue_def
      Scheduler_V611_Parse.tskTaskControlBlock_C_xGenericListItem_C_fl)

lemma scheduler_event_item_ptr_ptr_val [simp]:
  "ptr_val (scheduler_event_item_ptr tp) = ptr_val tp + 24"
  by (simp add: scheduler_event_item_ptr_def field_lvalue_def
      Scheduler_V611_Parse.tskTaskControlBlock_C_xEventListItem_C_fl)

lemma abi_scheduler_generic_item_ptr [simp]:
  "abi_item_ptr (scheduler_generic_item_ptr tp) =
   abi_generic_list_item_ptr tp"
  by (simp add: scheduler_generic_item_ptr_def
      abi_generic_list_item_ptr_def)

lemma abi_scheduler_event_item_ptr [simp]:
  "abi_item_ptr (scheduler_event_item_ptr tp) =
   abi_event_list_item_ptr tp"
  by (simp add: scheduler_event_item_ptr_def abi_event_list_item_ptr_def)

definition p2_physical_roots ::
  "scheduler_roots \<Rightarrow> Scheduler_V611_Parse.xLIST_C ptr list"
where
  "p2_physical_roots R =
    [sr_ready R 0, sr_ready R 1, sr_ready R 2, sr_ready R 3,
     sr_delayed_a R, sr_delayed_b R, sr_pending R, sr_suspended R]"

definition p2_tcb_ptrs ::
  "p2_tid scheduler_decode \<Rightarrow>
   Scheduler_V611_Parse.tskTaskControlBlock_C ptr list"
where
  "p2_tcb_ptrs D = [sd_tcb_ptr D P2_IDLE, sd_tcb_ptr D P2_RUN]"

definition scheduler_tcb_region ::
  "Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow> 32 word set"
where
  "scheduler_tcb_region tp =
    {ptr_val tp..+size_of TYPE(Scheduler_V611_Parse.tskTaskControlBlock_C)}"

lemma scheduler_tcb_region_size:
  "scheduler_tcb_region tp = {ptr_val tp..+68}"
  by (simp add: scheduler_tcb_region_def
      Scheduler_V611_Parse.tskTaskControlBlock_C_size)

definition p2_source_footprint ::
  "p2_tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow>
   heap_mem \<Rightarrow> bool"
where
  "p2_source_footprint D R h \<longleftrightarrow>
     R = generated_scheduler_roots \<and>
     distinct (p2_physical_roots R) \<and>
     (\<forall>lp \<in> set (p2_physical_roots R). c_guard lp) \<and>
     (\<forall>lp \<in> set (p2_physical_roots R).
       \<forall>lq \<in> set (p2_physical_roots R).
         lp \<noteq> lq \<longrightarrow>
           scheduler_list_region lp \<inter> scheduler_list_region lq = {}) \<and>
     distinct (p2_tcb_ptrs D) \<and>
     (\<forall>tp \<in> set (p2_tcb_ptrs D). c_guard tp) \<and>
     (\<forall>tp \<in> set (p2_tcb_ptrs D).
       \<forall>tq \<in> set (p2_tcb_ptrs D).
         tp \<noteq> tq \<longrightarrow>
           scheduler_tcb_region tp \<inter> scheduler_tcb_region tq = {}) \<and>
     (\<forall>tp \<in> set (p2_tcb_ptrs D).
       \<forall>lp \<in> set (p2_physical_roots R).
         scheduler_tcb_region tp \<inter> scheduler_list_region lp = {}) \<and>
     (\<forall>t \<in> {P2_IDLE, P2_RUN}.
        c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<and>
        c_guard (scheduler_event_item_ptr (sd_tcb_ptr D t)) \<and>
        scheduler_item_region
            (scheduler_generic_item_ptr (sd_tcb_ptr D t))
          \<subseteq> scheduler_tcb_region (sd_tcb_ptr D t) \<and>
        scheduler_item_region
            (scheduler_event_item_ptr (sd_tcb_ptr D t))
          \<subseteq> scheduler_tcb_region (sd_tcb_ptr D t) \<and>
        scheduler_item_region
            (scheduler_generic_item_ptr (sd_tcb_ptr D t))
          \<inter> scheduler_item_region
            (scheduler_event_item_ptr (sd_tcb_ptr D t)) = {}) \<and>
     raw_sentinel_max h (abi_list_ptr (sr_delayed_a R)) \<and>
     raw_sentinel_max h (abi_list_ptr (sr_delayed_b R))"

lemma p2_source_footprint_generated_rootsD:
  "p2_source_footprint D R h \<Longrightarrow> R = generated_scheduler_roots"
  by (simp add: p2_source_footprint_def)

lemma p2_source_footprint_run_guardsD:
  assumes footprint: "p2_source_footprint D R h"
  shows
    "c_guard (sd_tcb_ptr D P2_RUN) \<and>
     c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D P2_RUN)) \<and>
     c_guard (scheduler_event_item_ptr (sd_tcb_ptr D P2_RUN))"
  using footprint by (auto simp: p2_source_footprint_def p2_tcb_ptrs_def)

lemma p2_source_footprint_tcb_ptrs_distinctD:
  assumes footprint: "p2_source_footprint D R h"
  shows "sd_tcb_ptr D P2_IDLE \<noteq> sd_tcb_ptr D P2_RUN"
  using footprint
  by (simp add: p2_source_footprint_def p2_tcb_ptrs_def)

lemma p2_source_footprint_raw_root_guardD:
  assumes footprint: "p2_source_footprint D R h"
    and root: "lp \<in> set (p2_physical_roots R)"
  shows "c_guard (abi_list_ptr lp)"
proof -
  have "c_guard lp"
    using footprint root by (auto simp: p2_source_footprint_def)
  then show ?thesis by (simp add: abi_list_ptr_c_guard)
qed

lemma p2_source_footprint_generic_raw_guardD:
  assumes footprint: "p2_source_footprint D R h"
    and tid: "t \<in> {P2_IDLE, P2_RUN}"
  shows "c_guard (abi_generic_list_item_ptr (sd_tcb_ptr D t))"
proof -
  have scheduler_guard:
    "c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D t))"
    using footprint tid by (auto simp: p2_source_footprint_def)
  have
    "c_guard
       (abi_item_ptr (scheduler_generic_item_ptr (sd_tcb_ptr D t)))"
    using scheduler_guard
    by (rule iffD2[OF abi_item_ptr_c_guard])
  then show ?thesis by simp
qed

lemma p2_source_footprint_event_raw_guardD:
  assumes footprint: "p2_source_footprint D R h"
    and tid: "t \<in> {P2_IDLE, P2_RUN}"
  shows "c_guard (abi_event_list_item_ptr (sd_tcb_ptr D t))"
proof -
  have scheduler_guard:
    "c_guard (scheduler_event_item_ptr (sd_tcb_ptr D t))"
    using footprint tid by (auto simp: p2_source_footprint_def)
  have
    "c_guard
       (abi_item_ptr (scheduler_event_item_ptr (sd_tcb_ptr D t)))"
    using scheduler_guard
    by (rule iffD2[OF abi_item_ptr_c_guard])
  then show ?thesis by simp
qed

lemma p2_source_footprint_raw_roots_disjointD:
  assumes footprint: "p2_source_footprint D R h"
    and lp_root: "lp \<in> set (p2_physical_roots R)"
    and lq_root: "lq \<in> set (p2_physical_roots R)"
    and distinct: "lp \<noteq> lq"
  shows
    "raw_list_region (abi_list_ptr lp) \<inter>
       raw_list_region (abi_list_ptr lq) = {}"
proof -
  have scheduler_disjoint:
    "scheduler_list_region lp \<inter> scheduler_list_region lq = {}"
    using footprint lp_root lq_root distinct
    by (auto simp: p2_source_footprint_def)
  show ?thesis
    using scheduler_disjoint
    by (simp add: abi_list_region_eq)
qed

lemma p2_source_footprint_generic_item_root_disjointD:
  assumes footprint: "p2_source_footprint D R h"
    and tid: "t \<in> {P2_IDLE, P2_RUN}"
    and root: "lp \<in> set (p2_physical_roots R)"
  shows
    "raw_item_region
       (abi_generic_list_item_ptr (sd_tcb_ptr D t)) \<inter>
     raw_list_region (abi_list_ptr lp) = {}"
proof -
  have item_subset:
    "scheduler_item_region
       (scheduler_generic_item_ptr (sd_tcb_ptr D t))
     \<subseteq> scheduler_tcb_region (sd_tcb_ptr D t)"
    using footprint tid by (auto simp: p2_source_footprint_def)
  have tcb_root_disjoint:
    "scheduler_tcb_region (sd_tcb_ptr D t) \<inter>
       scheduler_list_region lp = {}"
    using footprint tid root
    by (auto simp: p2_source_footprint_def p2_tcb_ptrs_def)
  have scheduler_disjoint:
    "scheduler_item_region
       (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<inter>
     scheduler_list_region lp = {}"
    using item_subset tcb_root_disjoint by blast
  have item_region:
    "raw_item_region
       (abi_generic_list_item_ptr (sd_tcb_ptr D t)) =
     scheduler_item_region
       (scheduler_generic_item_ptr (sd_tcb_ptr D t))"
    using abi_item_region_eq[
      where p="scheduler_generic_item_ptr (sd_tcb_ptr D t)"]
    by simp
  show ?thesis
    using scheduler_disjoint
    by (simp add: item_region abi_list_region_eq)
qed

lemma p2_source_footprint_event_item_root_disjointD:
  assumes footprint: "p2_source_footprint D R h"
    and tid: "t \<in> {P2_IDLE, P2_RUN}"
    and root: "lp \<in> set (p2_physical_roots R)"
  shows
    "raw_item_region
       (abi_event_list_item_ptr (sd_tcb_ptr D t)) \<inter>
     raw_list_region (abi_list_ptr lp) = {}"
proof -
  have item_subset:
    "scheduler_item_region
       (scheduler_event_item_ptr (sd_tcb_ptr D t))
     \<subseteq> scheduler_tcb_region (sd_tcb_ptr D t)"
    using footprint tid by (auto simp: p2_source_footprint_def)
  have tcb_root_disjoint:
    "scheduler_tcb_region (sd_tcb_ptr D t) \<inter>
       scheduler_list_region lp = {}"
    using footprint tid root
    by (auto simp: p2_source_footprint_def p2_tcb_ptrs_def)
  have scheduler_disjoint:
    "scheduler_item_region
       (scheduler_event_item_ptr (sd_tcb_ptr D t)) \<inter>
     scheduler_list_region lp = {}"
    using item_subset tcb_root_disjoint by blast
  have item_region:
    "raw_item_region
       (abi_event_list_item_ptr (sd_tcb_ptr D t)) =
     scheduler_item_region
       (scheduler_event_item_ptr (sd_tcb_ptr D t))"
    using abi_item_region_eq[
      where p="scheduler_event_item_ptr (sd_tcb_ptr D t)"]
    by simp
  show ?thesis
    using scheduler_disjoint
    by (simp add: item_region abi_list_region_eq)
qed

lemma raw_item_list_disjoint_imp_not_end:
  assumes disjoint:
    "raw_item_region p \<inter> raw_list_region lp = {}"
  shows "p \<noteq> raw_end_item lp"
proof
  assume equal: "p = raw_end_item lp"
  have overlap:
    "ptr_val lp + of_nat 8 \<in>
       raw_item_region p \<inter> raw_list_region lp"
  proof (rule IntI)
    show "ptr_val lp + of_nat 8 \<in> raw_item_region p"
      unfolding raw_item_region_def equal raw_end_item_def
        raw_sentinel_ptr_def
      apply (simp add: field_lvalue_def xLIST_C_xListEnd_C_fl)
      apply (rule intvl_self)
      by (simp add: size_of_def)
    show "ptr_val lp + of_nat 8 \<in> raw_list_region lp"
      unfolding raw_list_region_def
      apply (rule intvlI)
      by (simp add: size_of_def)
  qed
  show False using disjoint overlap by blast
qed

lemma p2_source_footprint_generic_fresh_for_empty_rootD:
  assumes footprint: "p2_source_footprint D R h"
    and tid: "t \<in> {P2_IDLE, P2_RUN}"
    and root: "lp \<in> set (p2_physical_roots R)"
  shows
    "raw_fresh_for_insert (abi_list_ptr lp) []
       (abi_generic_list_item_ptr (sd_tcb_ptr D t))"
proof -
  have guard:
    "c_guard (abi_generic_list_item_ptr (sd_tcb_ptr D t))"
    by (rule p2_source_footprint_generic_raw_guardD[OF footprint tid])
  have disjoint:
    "raw_item_region
       (abi_generic_list_item_ptr (sd_tcb_ptr D t)) \<inter>
     raw_list_region (abi_list_ptr lp) = {}"
    by (rule p2_source_footprint_generic_item_root_disjointD[
          OF footprint tid root])
  have not_end:
    "abi_generic_list_item_ptr (sd_tcb_ptr D t) \<noteq>
     raw_end_item (abi_list_ptr lp)"
    by (rule raw_item_list_disjoint_imp_not_end[OF disjoint])
  show ?thesis
    using guard not_end disjoint
    by (simp add: raw_fresh_for_insert_def)
qed

lemma p2_source_footprint_run_generic_delayed_a_freshD:
  assumes footprint: "p2_source_footprint D R h"
  shows
    "raw_fresh_for_insert (abi_list_ptr (sr_delayed_a R)) []
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))"
  by (rule p2_source_footprint_generic_fresh_for_empty_rootD[
        OF footprint])
     (simp_all add: p2_physical_roots_def)

lemma p2_source_footprint_delayed_sentinel_maxD:
  assumes footprint: "p2_source_footprint D R h"
  shows
    "raw_sentinel_max h (abi_list_ptr (sr_delayed_a R)) \<and>
     raw_sentinel_max h (abi_list_ptr (sr_delayed_b R))"
  using footprint unfolding p2_source_footprint_def by blast

lemma p2_pre_delayed_a_ordered_emptyE:
  fixes c :: Scheduler_V611_Parse.globals
  assumes lists: "scheduler_lists_rel D R c p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
  obtains rx where
    "raw_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (abi_list_ptr (sr_delayed_a R)) rx"
    "ring rx = []"
    "cursor rx = None"
    "raw_sentinel_max
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (abi_list_ptr (sr_delayed_a R))"
    "raw_fresh_for_insert
       (abi_list_ptr (sr_delayed_a R)) (ring rx)
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))"
proof -
  let ?h =
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  from p2_pre_delayed_a_raw_emptyE[OF lists]
  obtain rx where
      rel:
        "raw_xlist_rel ?h (abi_list_ptr (sr_delayed_a R)) rx"
    and empty: "ring rx = []"
    and cursor: "cursor rx = None" .
  have sentinel:
    "raw_sentinel_max ?h (abi_list_ptr (sr_delayed_a R))"
    using p2_source_footprint_delayed_sentinel_maxD[OF footprint]
    by blast
  have fresh_empty:
    "raw_fresh_for_insert
       (abi_list_ptr (sr_delayed_a R)) []
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))"
    by (rule p2_source_footprint_run_generic_delayed_a_freshD[
          OF footprint])
  have fresh:
    "raw_fresh_for_insert
       (abi_list_ptr (sr_delayed_a R)) (ring rx)
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))"
    using fresh_empty empty by simp
  show ?thesis
    by (rule that[OF rel empty cursor sentinel fresh])
qed

end
