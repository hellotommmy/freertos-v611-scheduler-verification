theory Scheduler_P2_Frozen_Preimage
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Dynamic_Geometry.Scheduler_P2_Frozen_Dynamic_Geometry"
    "EAL6_FreeRTOS_V611_Scheduler_P2_Delay_Refinement.Scheduler_P2_Delay_Refinement"
begin

text \<open>
  G3b--G3c constructs one artifact-bound P2 preimage.  The two TCB addresses
  fixed in G3a are logical runtime addresses: this is not an allocator or boot
  reachability theorem.  The byte heap starts at zero.  It then writes exactly
  the eight raw list roots and the two live generic list items; in particular,
  the event items and every other unobserved byte of both 68-byte TCB regions
  remain explicitly zero.
\<close>

definition frozen_p2_raw_roots ::
  "List_V611_Raw_Skip_Translation.xLIST_C ptr list"
where
  "frozen_p2_raw_roots =
     map abi_list_ptr (p2_physical_roots generated_scheduler_roots)"

lemma frozen_p2_raw_roots [simp]:
  "frozen_p2_raw_roots =
    [Ptr 0x00102020, Ptr 0x00102034, Ptr 0x00102048,
     Ptr 0x0010205c, Ptr 0x0010208c, Ptr 0x001020a0,
     Ptr 0x001020bc, Ptr 0x001020d4]"
  by (simp add: frozen_p2_raw_roots_def abi_list_ptr_def)

lemma frozen_p2_raw_root_addresses [simp]:
  "abi_list_ptr (sr_ready generated_scheduler_roots 0) = Ptr 0x00102020 \<and>
   abi_list_ptr (sr_ready generated_scheduler_roots 1) = Ptr 0x00102034 \<and>
   abi_list_ptr (sr_ready generated_scheduler_roots 2) = Ptr 0x00102048 \<and>
   abi_list_ptr (sr_ready generated_scheduler_roots 3) = Ptr 0x0010205c \<and>
   abi_list_ptr (sr_delayed_a generated_scheduler_roots) = Ptr 0x0010208c \<and>
   abi_list_ptr (sr_delayed_b generated_scheduler_roots) = Ptr 0x001020a0 \<and>
   abi_list_ptr (sr_pending generated_scheduler_roots) = Ptr 0x001020bc \<and>
   abi_list_ptr (sr_suspended generated_scheduler_roots) = Ptr 0x001020d4"
  by (simp add: generated_scheduler_roots_def
      Scheduler_V611_Parse.pxReadyTasksLists_'_def
      Scheduler_V611_Parse.xDelayedTaskList1_'_def
      Scheduler_V611_Parse.xDelayedTaskList2_'_def
      Scheduler_V611_Parse.xPendingReadyList_'_def
      Scheduler_V611_Parse.xSuspendedTaskList_'_def
      array_ptr_index_def ptr_add_def Scheduler_V611_Parse.xLIST_C_size_of
      abi_list_ptr_def)

lemma frozen_p2_raw_generic_item_addresses [simp]:
  "abi_generic_list_item_ptr (sd_tcb_ptr frozen_p2_decode P2_IDLE) =
       Ptr 0x00200004 \<and>
   abi_generic_list_item_ptr (sd_tcb_ptr frozen_p2_decode P2_RUN) =
       Ptr 0x00200104"
  by (simp add: frozen_p2_decode_def abi_generic_list_item_ptr_def
      abi_item_ptr_def field_lvalue_def
      Scheduler_V611_Parse.tskTaskControlBlock_C_xGenericListItem_C_fl)

definition frozen_p2_empty_list_value ::
  "List_V611_Raw_Skip_Translation.xLIST_C ptr \<Rightarrow>
   List_V611_Raw_Skip_Translation.xLIST_C"
where
  "frozen_p2_empty_list_value lp =
    List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C_update
      (\<lambda>_. 0)
      (List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C_update
        (\<lambda>_. raw_end_item lp)
        (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C_update
          (\<lambda>_.
            List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.xItemValue_C_update
              (\<lambda>_. max_word)
              (List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxNext_C_update
                (\<lambda>_. raw_end_item lp)
                (List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxPrevious_C_update
                  (\<lambda>_. raw_end_item lp)
                  (undefined ::
                    List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C))))
          (undefined :: List_V611_Raw_Skip_Translation.xLIST_C)))"

definition frozen_p2_singleton_list_value ::
  "List_V611_Raw_Skip_Translation.xLIST_C ptr \<Rightarrow>
   List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr \<Rightarrow>
   List_V611_Raw_Skip_Translation.xLIST_C"
where
  "frozen_p2_singleton_list_value lp p =
    List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C_update
      (\<lambda>_. 1)
      (List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C_update
        (\<lambda>_. p)
        (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C_update
          (\<lambda>_.
            List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.xItemValue_C_update
              (\<lambda>_. max_word)
              (List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxNext_C_update
                (\<lambda>_. p)
                (List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxPrevious_C_update
                  (\<lambda>_. p)
                  (undefined ::
                    List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C))))
          (undefined :: List_V611_Raw_Skip_Translation.xLIST_C)))"

definition frozen_p2_linked_item_value ::
  "List_V611_Raw_Skip_Translation.xLIST_C ptr \<Rightarrow>
   List_V611_Raw_Skip_Translation.xLIST_ITEM_C"
where
  "frozen_p2_linked_item_value lp =
    List_V611_Raw_Skip_Translation.xLIST_ITEM_C.xItemValue_C_update
      (\<lambda>_. 0)
      (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxNext_C_update
        (\<lambda>_. raw_end_item lp)
        (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxPrevious_C_update
          (\<lambda>_. raw_end_item lp)
          (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C_update
            (\<lambda>_. NULL)
            (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C_update
              (\<lambda>_. PTR_COERCE(
                List_V611_Raw_Skip_Translation.xLIST_C \<rightarrow> unit) lp)
              (undefined ::
                List_V611_Raw_Skip_Translation.xLIST_ITEM_C)))))"

lemma frozen_p2_empty_list_value_fields [simp]:
  "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
      (frozen_p2_empty_list_value lp) = 0 \<and>
   List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C
      (frozen_p2_empty_list_value lp) = raw_end_item lp \<and>
   List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.xItemValue_C
      (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
        (frozen_p2_empty_list_value lp)) = max_word \<and>
   List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxNext_C
      (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
        (frozen_p2_empty_list_value lp)) = raw_end_item lp \<and>
   List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxPrevious_C
      (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
        (frozen_p2_empty_list_value lp)) = raw_end_item lp"
  by (simp add: frozen_p2_empty_list_value_def)

lemma frozen_p2_singleton_list_value_fields [simp]:
  "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
      (frozen_p2_singleton_list_value lp p) = 1 \<and>
   List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C
      (frozen_p2_singleton_list_value lp p) = p \<and>
   List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.xItemValue_C
      (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
        (frozen_p2_singleton_list_value lp p)) = max_word \<and>
   List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxNext_C
      (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
        (frozen_p2_singleton_list_value lp p)) = p \<and>
   List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxPrevious_C
      (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
        (frozen_p2_singleton_list_value lp p)) = p"
  by (simp add: frozen_p2_singleton_list_value_def)

lemma frozen_p2_linked_item_value_fields [simp]:
  "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.xItemValue_C
      (frozen_p2_linked_item_value lp) = 0 \<and>
   List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxNext_C
      (frozen_p2_linked_item_value lp) = raw_end_item lp \<and>
   List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxPrevious_C
      (frozen_p2_linked_item_value lp) = raw_end_item lp \<and>
   List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
      (frozen_p2_linked_item_value lp) = NULL \<and>
   List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
      (frozen_p2_linked_item_value lp) =
        PTR_COERCE(List_V611_Raw_Skip_Translation.xLIST_C \<rightarrow> unit) lp"
  by (simp add: frozen_p2_linked_item_value_def)

definition frozen_p2_zero_heap :: heap_mem where
  "frozen_p2_zero_heap = (\<lambda>_. 0)"

definition frozen_p2_root_heap :: heap_mem where
  "frozen_p2_root_heap =
    heap_update (abi_list_ptr (sr_suspended generated_scheduler_roots))
      (frozen_p2_empty_list_value
        (abi_list_ptr (sr_suspended generated_scheduler_roots)))
    (heap_update (abi_list_ptr (sr_pending generated_scheduler_roots))
      (frozen_p2_empty_list_value
        (abi_list_ptr (sr_pending generated_scheduler_roots)))
    (heap_update (abi_list_ptr (sr_delayed_b generated_scheduler_roots))
      (frozen_p2_empty_list_value
        (abi_list_ptr (sr_delayed_b generated_scheduler_roots)))
    (heap_update (abi_list_ptr (sr_delayed_a generated_scheduler_roots))
      (frozen_p2_empty_list_value
        (abi_list_ptr (sr_delayed_a generated_scheduler_roots)))
    (heap_update (abi_list_ptr (sr_ready generated_scheduler_roots 3))
      (frozen_p2_empty_list_value
        (abi_list_ptr (sr_ready generated_scheduler_roots 3)))
    (heap_update (abi_list_ptr (sr_ready generated_scheduler_roots 2))
      (frozen_p2_singleton_list_value
        (abi_list_ptr (sr_ready generated_scheduler_roots 2))
        (abi_generic_list_item_ptr
          (sd_tcb_ptr frozen_p2_decode P2_RUN)))
    (heap_update (abi_list_ptr (sr_ready generated_scheduler_roots 1))
      (frozen_p2_empty_list_value
        (abi_list_ptr (sr_ready generated_scheduler_roots 1)))
    (heap_update (abi_list_ptr (sr_ready generated_scheduler_roots 0))
      (frozen_p2_singleton_list_value
        (abi_list_ptr (sr_ready generated_scheduler_roots 0))
        (abi_generic_list_item_ptr
          (sd_tcb_ptr frozen_p2_decode P2_IDLE)))
      frozen_p2_zero_heap)))))))"

definition frozen_p2_heap :: heap_mem where
  "frozen_p2_heap =
    heap_update
      (abi_generic_list_item_ptr (sd_tcb_ptr frozen_p2_decode P2_RUN))
      (frozen_p2_linked_item_value
        (abi_list_ptr (sr_ready generated_scheduler_roots 2)))
      (heap_update
        (abi_generic_list_item_ptr (sd_tcb_ptr frozen_p2_decode P2_IDLE))
        (frozen_p2_linked_item_value
          (abi_list_ptr (sr_ready generated_scheduler_roots 0)))
        frozen_p2_root_heap)"

lemma frozen_p2_raw_roots_guarded:
  assumes root: "lp \<in> set frozen_p2_raw_roots"
  shows "c_guard lp \<and> c_guard (raw_end_item lp)"
proof -
  from root obtain sp where
      sp: "sp \<in> set (p2_physical_roots generated_scheduler_roots)"
    and lp: "lp = abi_list_ptr sp"
    unfolding frozen_p2_raw_roots_def by auto
  have scheduler_guard: "c_guard sp"
    using frozen_p2_physical_roots_guarded sp by blast
  have raw_guard: "c_guard (abi_list_ptr sp)"
    using scheduler_guard by (rule iffD2[OF abi_list_ptr_c_guard])
  have list_guard: "c_guard lp"
    using raw_guard lp by simp
  from root have cases:
    "lp = Ptr 0x00102020 \<or> lp = Ptr 0x00102034 \<or>
     lp = Ptr 0x00102048 \<or> lp = Ptr 0x0010205c \<or>
     lp = Ptr 0x0010208c \<or> lp = Ptr 0x001020a0 \<or>
     lp = Ptr 0x001020bc \<or> lp = Ptr 0x001020d4"
    by simp
  have end_guard: "c_guard (raw_end_item lp)"
    using cases
    apply (elim disjE)
    apply (all \<open>hypsubst\<close>)
    apply (all \<open>unfold raw_end_item_def raw_sentinel_ptr_def;
      simp add: field_lvalue_def
        List_V611_Raw_Skip_Translation.xLIST_C_xListEnd_C_fl;
      rule frozen_item_guardI;
      simp add: addr_card_def card_word\<close>)
    done
  show ?thesis using list_guard end_guard by blast
qed

lemma frozen_p2_raw_root_regions_disjoint:
  assumes lp: "lp \<in> set frozen_p2_raw_roots"
    and lq: "lq \<in> set frozen_p2_raw_roots"
    and ne: "lp \<noteq> lq"
  shows "raw_list_region lp \<inter> raw_list_region lq = {}"
proof -
  from lp obtain sp where
      sp: "sp \<in> set (p2_physical_roots generated_scheduler_roots)"
    and lp_eq: "lp = abi_list_ptr sp"
    unfolding frozen_p2_raw_roots_def by auto
  from lq obtain sq where
      sq: "sq \<in> set (p2_physical_roots generated_scheduler_roots)"
    and lq_eq: "lq = abi_list_ptr sq"
    unfolding frozen_p2_raw_roots_def by auto
  have sp_ne: "sp \<noteq> sq"
    using ne lp_eq lq_eq by auto
  have disjoint:
    "scheduler_list_region sp \<inter> scheduler_list_region sq = {}"
    using frozen_p2_physical_roots_pairwise_disjoint sp sq sp_ne by blast
  show ?thesis
    using disjoint lp_eq lq_eq by (simp add: abi_list_region_eq)
qed

lemma frozen_p2_generic_item_root_disjoint:
  assumes tid: "t \<in> {P2_IDLE, P2_RUN}"
    and root: "lp \<in> set frozen_p2_raw_roots"
  shows
    "raw_item_region
       (abi_generic_list_item_ptr (sd_tcb_ptr frozen_p2_decode t)) \<inter>
     raw_list_region lp = {}"
proof -
  from root obtain sp where
      sp: "sp \<in> set (p2_physical_roots generated_scheduler_roots)"
    and lp: "lp = abi_list_ptr sp"
    unfolding frozen_p2_raw_roots_def by auto
  have tp:
    "sd_tcb_ptr frozen_p2_decode t \<in>
       set (p2_tcb_ptrs frozen_p2_decode)"
    using tid by (cases t) (simp_all add: p2_tcb_ptrs_def)
  have item_subset:
    "scheduler_item_region
       (scheduler_generic_item_ptr (sd_tcb_ptr frozen_p2_decode t))
     \<subseteq> scheduler_tcb_region (sd_tcb_ptr frozen_p2_decode t)"
    using frozen_p2_embedded_geometry tid by blast
  have tcb_root:
    "scheduler_tcb_region (sd_tcb_ptr frozen_p2_decode t) \<inter>
       scheduler_list_region sp = {}"
    using frozen_p2_tcb_root_separation tp sp by blast
  have scheduler_disjoint:
    "scheduler_item_region
       (scheduler_generic_item_ptr (sd_tcb_ptr frozen_p2_decode t)) \<inter>
     scheduler_list_region sp = {}"
    using item_subset tcb_root by blast
  have raw_item:
    "raw_item_region
       (abi_generic_list_item_ptr (sd_tcb_ptr frozen_p2_decode t)) =
     scheduler_item_region
       (scheduler_generic_item_ptr (sd_tcb_ptr frozen_p2_decode t))"
    using abi_item_region_eq[
      where p="scheduler_generic_item_ptr
        (sd_tcb_ptr frozen_p2_decode t)"]
    by simp
  show ?thesis
    using scheduler_disjoint lp raw_item
    by (simp add: abi_list_region_eq)
qed

lemma frozen_p2_generic_item_guarded:
  assumes tid: "t \<in> {P2_IDLE, P2_RUN}"
  shows
    "c_guard
      (abi_generic_list_item_ptr (sd_tcb_ptr frozen_p2_decode t))"
proof -
  have scheduler_guard:
    "c_guard
      (scheduler_generic_item_ptr (sd_tcb_ptr frozen_p2_decode t))"
    using frozen_p2_embedded_geometry tid by blast
  have raw_guard:
    "c_guard
      (abi_item_ptr
        (scheduler_generic_item_ptr (sd_tcb_ptr frozen_p2_decode t)))"
    using scheduler_guard by (rule iffD2[OF abi_item_ptr_c_guard])
  show ?thesis using raw_guard by simp
qed

lemma frozen_p2_root_update_frame:
  assumes lp: "lp \<in> set frozen_p2_raw_roots"
    and lq: "lq \<in> set frozen_p2_raw_roots"
    and ne: "lp \<noteq> lq"
  shows
    "h_val
       (heap_update lq
         (v :: List_V611_Raw_Skip_Translation.xLIST_C) h) lp =
     h_val h lp"
  apply (rule h_val_heap_update_disjoint)
  using frozen_p2_raw_root_regions_disjoint[OF lp lq ne]
  by (simp add: raw_list_region_def)

lemma frozen_p2_generic_item_update_root_frame:
  assumes tid: "t \<in> {P2_IDLE, P2_RUN}"
    and root: "lp \<in> set frozen_p2_raw_roots"
  shows
    "h_val
       (heap_update
         (abi_generic_list_item_ptr (sd_tcb_ptr frozen_p2_decode t))
         (v :: List_V611_Raw_Skip_Translation.xLIST_ITEM_C) h) lp =
     h_val h lp"
  apply (rule h_val_heap_update_disjoint)
  using frozen_p2_generic_item_root_disjoint[OF tid root]
  by (simp add: raw_list_region_def raw_item_region_def Int_commute)

lemma frozen_p2_run_item_update_idle_frame:
  "h_val
     (heap_update
       (abi_generic_list_item_ptr (sd_tcb_ptr frozen_p2_decode P2_RUN))
       (v :: List_V611_Raw_Skip_Translation.xLIST_ITEM_C) h)
     (abi_generic_list_item_ptr (sd_tcb_ptr frozen_p2_decode P2_IDLE)) =
   h_val h
     (abi_generic_list_item_ptr (sd_tcb_ptr frozen_p2_decode P2_IDLE))"
proof -
  have idle_item:
    "abi_generic_list_item_ptr (sd_tcb_ptr frozen_p2_decode P2_IDLE) =
       Ptr 0x00200004"
    using frozen_p2_raw_generic_item_addresses by blast
  have run_item:
    "abi_generic_list_item_ptr (sd_tcb_ptr frozen_p2_decode P2_RUN) =
       Ptr 0x00200104"
    using frozen_p2_raw_generic_item_addresses by blast
  show ?thesis
    apply (rule h_val_heap_update_disjoint)
    apply (rule intvl_disjoint1)
    by (simp_all add: idle_item run_item
        List_V611_Raw_Skip_Translation.xLIST_ITEM_C_size_of)
qed

lemmas frozen_p2_root_address_simps =
  generated_scheduler_roots_def
  Scheduler_V611_Parse.pxReadyTasksLists_'_def
  Scheduler_V611_Parse.xDelayedTaskList1_'_def
  Scheduler_V611_Parse.xDelayedTaskList2_'_def
  Scheduler_V611_Parse.xPendingReadyList_'_def
  Scheduler_V611_Parse.xSuspendedTaskList_'_def
  array_ptr_index_def ptr_add_def Scheduler_V611_Parse.xLIST_C_size_of
  abi_list_ptr_def

lemma frozen_p2_root_heap_ready0 [simp]:
  "h_val frozen_p2_root_heap
      (abi_list_ptr (sr_ready generated_scheduler_roots 0)) =
    frozen_p2_singleton_list_value
      (abi_list_ptr (sr_ready generated_scheduler_roots 0))
      (abi_generic_list_item_ptr
        (sd_tcb_ptr frozen_p2_decode P2_IDLE))"
  unfolding frozen_p2_root_heap_def
  by (simp add: frozen_p2_root_update_frame frozen_p2_root_address_simps)

lemma frozen_p2_root_heap_ready1 [simp]:
  "h_val frozen_p2_root_heap
      (abi_list_ptr (sr_ready generated_scheduler_roots 1)) =
    frozen_p2_empty_list_value
      (abi_list_ptr (sr_ready generated_scheduler_roots 1))"
  unfolding frozen_p2_root_heap_def
  by (simp add: frozen_p2_root_update_frame frozen_p2_root_address_simps)

lemma frozen_p2_root_heap_ready2 [simp]:
  "h_val frozen_p2_root_heap
      (abi_list_ptr (sr_ready generated_scheduler_roots 2)) =
    frozen_p2_singleton_list_value
      (abi_list_ptr (sr_ready generated_scheduler_roots 2))
      (abi_generic_list_item_ptr
        (sd_tcb_ptr frozen_p2_decode P2_RUN))"
  unfolding frozen_p2_root_heap_def
  by (simp add: frozen_p2_root_update_frame frozen_p2_root_address_simps)

lemma frozen_p2_root_heap_ready3 [simp]:
  "h_val frozen_p2_root_heap
      (abi_list_ptr (sr_ready generated_scheduler_roots 3)) =
    frozen_p2_empty_list_value
      (abi_list_ptr (sr_ready generated_scheduler_roots 3))"
  unfolding frozen_p2_root_heap_def
  by (simp add: frozen_p2_root_update_frame frozen_p2_root_address_simps)

lemma frozen_p2_root_heap_delayed_a [simp]:
  "h_val frozen_p2_root_heap
      (abi_list_ptr (sr_delayed_a generated_scheduler_roots)) =
    frozen_p2_empty_list_value
      (abi_list_ptr (sr_delayed_a generated_scheduler_roots))"
  unfolding frozen_p2_root_heap_def
  by (simp add: frozen_p2_root_update_frame frozen_p2_root_address_simps)

lemma frozen_p2_root_heap_delayed_b [simp]:
  "h_val frozen_p2_root_heap
      (abi_list_ptr (sr_delayed_b generated_scheduler_roots)) =
    frozen_p2_empty_list_value
      (abi_list_ptr (sr_delayed_b generated_scheduler_roots))"
  unfolding frozen_p2_root_heap_def
  by (simp add: frozen_p2_root_update_frame frozen_p2_root_address_simps)

lemma frozen_p2_root_heap_pending [simp]:
  "h_val frozen_p2_root_heap
      (abi_list_ptr (sr_pending generated_scheduler_roots)) =
    frozen_p2_empty_list_value
      (abi_list_ptr (sr_pending generated_scheduler_roots))"
  unfolding frozen_p2_root_heap_def
  by (simp add: frozen_p2_root_update_frame frozen_p2_root_address_simps)

lemma frozen_p2_root_heap_suspended [simp]:
  "h_val frozen_p2_root_heap
      (abi_list_ptr (sr_suspended generated_scheduler_roots)) =
    frozen_p2_empty_list_value
      (abi_list_ptr (sr_suspended generated_scheduler_roots))"
  unfolding frozen_p2_root_heap_def
  by (simp add: frozen_p2_root_update_frame frozen_p2_root_address_simps)

lemma frozen_p2_root_heap_readbacks [simp]:
  "h_val frozen_p2_root_heap
      (abi_list_ptr (sr_ready generated_scheduler_roots 0)) =
      frozen_p2_singleton_list_value
        (abi_list_ptr (sr_ready generated_scheduler_roots 0))
        (abi_generic_list_item_ptr
          (sd_tcb_ptr frozen_p2_decode P2_IDLE)) \<and>
   h_val frozen_p2_root_heap
      (abi_list_ptr (sr_ready generated_scheduler_roots 1)) =
      frozen_p2_empty_list_value
        (abi_list_ptr (sr_ready generated_scheduler_roots 1)) \<and>
   h_val frozen_p2_root_heap
      (abi_list_ptr (sr_ready generated_scheduler_roots 2)) =
      frozen_p2_singleton_list_value
        (abi_list_ptr (sr_ready generated_scheduler_roots 2))
        (abi_generic_list_item_ptr
          (sd_tcb_ptr frozen_p2_decode P2_RUN)) \<and>
   h_val frozen_p2_root_heap
      (abi_list_ptr (sr_ready generated_scheduler_roots 3)) =
      frozen_p2_empty_list_value
        (abi_list_ptr (sr_ready generated_scheduler_roots 3)) \<and>
   h_val frozen_p2_root_heap
      (abi_list_ptr (sr_delayed_a generated_scheduler_roots)) =
      frozen_p2_empty_list_value
        (abi_list_ptr (sr_delayed_a generated_scheduler_roots)) \<and>
   h_val frozen_p2_root_heap
      (abi_list_ptr (sr_delayed_b generated_scheduler_roots)) =
      frozen_p2_empty_list_value
        (abi_list_ptr (sr_delayed_b generated_scheduler_roots)) \<and>
   h_val frozen_p2_root_heap
      (abi_list_ptr (sr_pending generated_scheduler_roots)) =
      frozen_p2_empty_list_value
        (abi_list_ptr (sr_pending generated_scheduler_roots)) \<and>
   h_val frozen_p2_root_heap
      (abi_list_ptr (sr_suspended generated_scheduler_roots)) =
      frozen_p2_empty_list_value
        (abi_list_ptr (sr_suspended generated_scheduler_roots))"
  using frozen_p2_root_heap_ready0 frozen_p2_root_heap_ready1
    frozen_p2_root_heap_ready2 frozen_p2_root_heap_ready3
    frozen_p2_root_heap_delayed_a frozen_p2_root_heap_delayed_b
    frozen_p2_root_heap_pending frozen_p2_root_heap_suspended
  by blast

lemma frozen_p2_heap_root_readbacks [simp]:
  "h_val frozen_p2_heap lp = h_val frozen_p2_root_heap lp"
  if root: "lp \<in> set frozen_p2_raw_roots"
proof -
  let ?idle_heap =
    "heap_update
      (abi_generic_list_item_ptr (sd_tcb_ptr frozen_p2_decode P2_IDLE))
      (frozen_p2_linked_item_value
        (abi_list_ptr (sr_ready generated_scheduler_roots 0)))
      frozen_p2_root_heap"
  have run_frame: "h_val frozen_p2_heap lp = h_val ?idle_heap lp"
    unfolding frozen_p2_heap_def
    apply (rule frozen_p2_generic_item_update_root_frame)
     apply simp
    apply (rule root)
    done
  have idle_frame: "h_val ?idle_heap lp = h_val frozen_p2_root_heap lp"
    apply (rule frozen_p2_generic_item_update_root_frame)
     apply simp
    apply (rule root)
    done
  show ?thesis using run_frame idle_frame by simp
qed

lemma frozen_p2_heap_root_value:
  assumes root: "lp \<in> set frozen_p2_raw_roots"
    and root_read: "h_val frozen_p2_root_heap lp = v"
  shows "h_val frozen_p2_heap lp = v"
  using frozen_p2_heap_root_readbacks[OF root] root_read by simp

lemma frozen_p2_heap_delayed_a [simp]:
  "h_val frozen_p2_heap
      (abi_list_ptr (sr_delayed_a generated_scheduler_roots)) =
    frozen_p2_empty_list_value
      (abi_list_ptr (sr_delayed_a generated_scheduler_roots))"
  apply (rule frozen_p2_heap_root_value)
   apply (simp add: frozen_p2_root_address_simps)
  apply (rule frozen_p2_root_heap_delayed_a)
  done

lemma frozen_p2_heap_delayed_b [simp]:
  "h_val frozen_p2_heap
      (abi_list_ptr (sr_delayed_b generated_scheduler_roots)) =
    frozen_p2_empty_list_value
      (abi_list_ptr (sr_delayed_b generated_scheduler_roots))"
  apply (rule frozen_p2_heap_root_value)
   apply (simp add: frozen_p2_root_address_simps)
  apply (rule frozen_p2_root_heap_delayed_b)
  done

lemma frozen_p2_heap_idle_item [simp]:
  "h_val frozen_p2_heap
      (abi_generic_list_item_ptr (sd_tcb_ptr frozen_p2_decode P2_IDLE)) =
    frozen_p2_linked_item_value
      (abi_list_ptr (sr_ready generated_scheduler_roots 0))"
  unfolding frozen_p2_heap_def
  apply (subst frozen_p2_run_item_update_idle_frame)
  by simp

lemma frozen_p2_heap_run_item [simp]:
  "h_val frozen_p2_heap
      (abi_generic_list_item_ptr (sd_tcb_ptr frozen_p2_decode P2_RUN)) =
    frozen_p2_linked_item_value
      (abi_list_ptr (sr_ready generated_scheduler_roots 2))"
  unfolding frozen_p2_heap_def
  by simp

lemma frozen_p2_heap_item_readbacks [simp]:
  "h_val frozen_p2_heap
      (abi_generic_list_item_ptr (sd_tcb_ptr frozen_p2_decode P2_IDLE)) =
      frozen_p2_linked_item_value
        (abi_list_ptr (sr_ready generated_scheduler_roots 0)) \<and>
   h_val frozen_p2_heap
      (abi_generic_list_item_ptr (sd_tcb_ptr frozen_p2_decode P2_RUN)) =
      frozen_p2_linked_item_value
        (abi_list_ptr (sr_ready generated_scheduler_roots 2))"
  using frozen_p2_heap_idle_item frozen_p2_heap_run_item by blast

lemma frozen_p2_empty_layout:
  assumes root: "lp \<in> set frozen_p2_raw_roots"
  shows "raw_xlist_layout lp []"
  using frozen_p2_raw_roots_guarded[OF root]
  by (simp add: raw_xlist_layout_def)

lemma frozen_p2_singleton_layout:
  assumes tid: "t \<in> {P2_IDLE, P2_RUN}"
    and root: "lp \<in> set frozen_p2_raw_roots"
  shows
    "raw_xlist_layout lp
      [abi_generic_list_item_ptr (sd_tcb_ptr frozen_p2_decode t)]"
proof -
  let ?p =
    "abi_generic_list_item_ptr (sd_tcb_ptr frozen_p2_decode t)"
  have root_guards: "c_guard lp \<and> c_guard (raw_end_item lp)"
    by (rule frozen_p2_raw_roots_guarded[OF root])
  from root_guards have root_guard: "c_guard lp"
    by blast
  from root_guards have end_guard: "c_guard (raw_end_item lp)"
    by blast
  have item_guard: "c_guard ?p"
    by (rule frozen_p2_generic_item_guarded[OF tid])
  have disjoint: "raw_item_region ?p \<inter> raw_list_region lp = {}"
    by (rule frozen_p2_generic_item_root_disjoint[OF tid root])
  have not_end: "?p \<noteq> raw_end_item lp"
    by (rule raw_item_list_disjoint_imp_not_end[OF disjoint])
  show ?thesis
    using root_guard end_guard item_guard disjoint not_end
    by (simp add: raw_xlist_layout_def)
qed

definition frozen_p2_raw_keys ::
  "List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr \<Rightarrow> 32 word"
where
  "frozen_p2_raw_keys = (\<lambda>_. 0)"

lemma frozen_p2_empty_raw_rel:
  assumes root: "lp \<in> set frozen_p2_raw_roots"
    and root_value:
      "h_val frozen_p2_heap lp = frozen_p2_empty_list_value lp"
  shows
    "raw_xlist_rel frozen_p2_heap lp
      (raw_empty_abs frozen_p2_raw_keys)"
  apply (rule raw_xlist_rel_emptyI)
  subgoal by (rule frozen_p2_empty_layout[OF root])
  using root_value
  by (simp_all add: frozen_p2_empty_list_value_def)

lemma frozen_p2_singleton_raw_rel:
  assumes tid: "t \<in> {P2_IDLE, P2_RUN}"
    and root: "lp \<in> set frozen_p2_raw_roots"
    and root_value:
      "h_val frozen_p2_heap lp = frozen_p2_singleton_list_value lp p"
    and item: "p = abi_generic_list_item_ptr
      (sd_tcb_ptr frozen_p2_decode t)"
    and item_value:
      "h_val frozen_p2_heap p = frozen_p2_linked_item_value lp"
  shows
    "raw_xlist_rel frozen_p2_heap lp
      (raw_singleton_abs p frozen_p2_raw_keys 0)"
  apply (rule raw_xlist_rel_singletonI)
  subgoal
    apply (subst item)
    by (rule frozen_p2_singleton_layout[OF tid root])
  using root_value item_value
  by (simp_all add: frozen_p2_singleton_list_value_def
      frozen_p2_linked_item_value_def)

lemma frozen_p2_ready0_raw_rel:
  "raw_xlist_rel frozen_p2_heap
     (abi_list_ptr (sr_ready generated_scheduler_roots 0))
     (raw_singleton_abs
       (abi_generic_list_item_ptr
         (sd_tcb_ptr frozen_p2_decode P2_IDLE))
       frozen_p2_raw_keys 0)"
  apply (rule frozen_p2_singleton_raw_rel[where t=P2_IDLE])
  subgoal by simp
  subgoal by (simp add: frozen_p2_root_address_simps)
  subgoal
    apply (rule frozen_p2_heap_root_value)
     apply (simp add: frozen_p2_root_address_simps)
    apply (rule frozen_p2_root_heap_ready0)
    done
  subgoal by simp
  subgoal by (rule frozen_p2_heap_idle_item)
  done

lemma frozen_p2_ready2_raw_rel:
  "raw_xlist_rel frozen_p2_heap
     (abi_list_ptr (sr_ready generated_scheduler_roots 2))
     (raw_singleton_abs
       (abi_generic_list_item_ptr
         (sd_tcb_ptr frozen_p2_decode P2_RUN))
       frozen_p2_raw_keys 0)"
  apply (rule frozen_p2_singleton_raw_rel[where t=P2_RUN])
  subgoal by simp
  subgoal by (simp add: frozen_p2_root_address_simps)
  subgoal
    apply (rule frozen_p2_heap_root_value)
     apply (simp add: frozen_p2_root_address_simps)
    apply (rule frozen_p2_root_heap_ready2)
    done
  subgoal by simp
  subgoal by (rule frozen_p2_heap_run_item)
  done

lemma frozen_p2_ready1_raw_rel:
  "raw_xlist_rel frozen_p2_heap
     (abi_list_ptr (sr_ready generated_scheduler_roots 1))
     (raw_empty_abs frozen_p2_raw_keys)"
  apply (rule frozen_p2_empty_raw_rel)
  subgoal by (simp add: frozen_p2_root_address_simps)
  subgoal
    apply (rule frozen_p2_heap_root_value)
     apply (simp add: frozen_p2_root_address_simps)
    apply (rule frozen_p2_root_heap_ready1)
    done
  done

lemma frozen_p2_ready3_raw_rel:
  "raw_xlist_rel frozen_p2_heap
     (abi_list_ptr (sr_ready generated_scheduler_roots 3))
     (raw_empty_abs frozen_p2_raw_keys)"
  apply (rule frozen_p2_empty_raw_rel)
  subgoal by (simp add: frozen_p2_root_address_simps)
  subgoal
    apply (rule frozen_p2_heap_root_value)
     apply (simp add: frozen_p2_root_address_simps)
    apply (rule frozen_p2_root_heap_ready3)
    done
  done

lemma frozen_p2_delayed_a_raw_rel:
  "raw_xlist_rel frozen_p2_heap
     (abi_list_ptr (sr_delayed_a generated_scheduler_roots))
     (raw_empty_abs frozen_p2_raw_keys)"
  apply (rule frozen_p2_empty_raw_rel)
  subgoal by (simp add: frozen_p2_root_address_simps)
  subgoal
    apply (rule frozen_p2_heap_root_value)
     apply (simp add: frozen_p2_root_address_simps)
    apply (rule frozen_p2_root_heap_delayed_a)
    done
  done

lemma frozen_p2_delayed_b_raw_rel:
  "raw_xlist_rel frozen_p2_heap
     (abi_list_ptr (sr_delayed_b generated_scheduler_roots))
     (raw_empty_abs frozen_p2_raw_keys)"
  apply (rule frozen_p2_empty_raw_rel)
  subgoal by (simp add: frozen_p2_root_address_simps)
  subgoal
    apply (rule frozen_p2_heap_root_value)
     apply (simp add: frozen_p2_root_address_simps)
    apply (rule frozen_p2_root_heap_delayed_b)
    done
  done

lemma frozen_p2_pending_raw_rel:
  "raw_xlist_rel frozen_p2_heap
     (abi_list_ptr (sr_pending generated_scheduler_roots))
     (raw_empty_abs frozen_p2_raw_keys)"
  apply (rule frozen_p2_empty_raw_rel)
  subgoal by (simp add: frozen_p2_root_address_simps)
  subgoal
    apply (rule frozen_p2_heap_root_value)
     apply (simp add: frozen_p2_root_address_simps)
    apply (rule frozen_p2_root_heap_pending)
    done
  done

lemma frozen_p2_suspended_raw_rel:
  "raw_xlist_rel frozen_p2_heap
     (abi_list_ptr (sr_suspended generated_scheduler_roots))
     (raw_empty_abs frozen_p2_raw_keys)"
  apply (rule frozen_p2_empty_raw_rel)
  subgoal by (simp add: frozen_p2_root_address_simps)
  subgoal
    apply (rule frozen_p2_heap_root_value)
     apply (simp add: frozen_p2_root_address_simps)
    apply (rule frozen_p2_root_heap_suspended)
    done
  done

lemma frozen_p2_idle_node_decode [simp]:
  "sd_node_decode frozen_p2_decode
      (abi_generic_list_item_ptr
        (sd_tcb_ptr frozen_p2_decode P2_IDLE)) =
    Some (Generic P2_IDLE)"
  using scheduler_node_decode_Generic_iff[
      OF frozen_p2_decoder_rel,
      of "abi_generic_list_item_ptr
        (sd_tcb_ptr frozen_p2_decode P2_IDLE)" P2_IDLE]
  by (simp add: p2_pre_def)

lemma frozen_p2_run_node_decode [simp]:
  "sd_node_decode frozen_p2_decode
      (abi_generic_list_item_ptr
        (sd_tcb_ptr frozen_p2_decode P2_RUN)) =
    Some (Generic P2_RUN)"
  using scheduler_node_decode_Generic_iff[
      OF frozen_p2_decoder_rel,
      of "abi_generic_list_item_ptr
        (sd_tcb_ptr frozen_p2_decode P2_RUN)" P2_RUN]
  by (simp add: p2_pre_def)

lemma frozen_p2_idle_node_decode_address [simp]:
  "sd_node_decode frozen_p2_decode
      (Ptr 0x00200004 ::
        List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr) =
    Some (Generic P2_IDLE)"
proof -
  have pointer:
    "abi_generic_list_item_ptr
        (sd_tcb_ptr frozen_p2_decode P2_IDLE) = Ptr 0x00200004"
    using frozen_p2_raw_generic_item_addresses by blast
  show ?thesis using frozen_p2_idle_node_decode pointer by simp
qed

lemma frozen_p2_run_node_decode_address [simp]:
  "sd_node_decode frozen_p2_decode
      (Ptr 0x00200104 ::
        List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr) =
    Some (Generic P2_RUN)"
proof -
  have pointer:
    "abi_generic_list_item_ptr
        (sd_tcb_ptr frozen_p2_decode P2_RUN) = Ptr 0x00200104"
    using frozen_p2_raw_generic_item_addresses by blast
  show ?thesis using frozen_p2_run_node_decode pointer by simp
qed

lemma frozen_p2_ready0_sched_rel:
  "sched_xlist_rel (sd_node_decode frozen_p2_decode) frozen_p2_heap
     (abi_list_ptr (sr_ready generated_scheduler_roots 0))
     (sa_ready p2_pre 0)"
  apply (rule sched_xlist_rel_ready_singletonI[
        OF frozen_p2_ready0_raw_rel,
        where p="abi_generic_list_item_ptr
          (sd_tcb_ptr frozen_p2_decode P2_IDLE)" and t=P2_IDLE])
  subgoal by (simp add: raw_singleton_abs_def raw_empty_abs_def
        list_insert_end_abs_def)
  subgoal by (simp add: raw_singleton_abs_def raw_empty_abs_def
        list_insert_end_abs_def)
  subgoal by (simp add: p2_pre_def p2_idle_ready_def
        empty_node_ring_def list_insert_end_abs_def)
  subgoal by (simp add: p2_pre_def p2_idle_ready_def
        empty_node_ring_def list_insert_end_abs_def)
  subgoal by (rule frozen_p2_idle_node_decode)
  subgoal by (simp add: raw_singleton_abs_def raw_empty_abs_def p2_pre_def
        p2_idle_ready_def empty_node_ring_def list_insert_end_abs_def
        frozen_p2_raw_keys_def)
  done

lemma frozen_p2_ready2_sched_rel:
  "sched_xlist_rel (sd_node_decode frozen_p2_decode) frozen_p2_heap
     (abi_list_ptr (sr_ready generated_scheduler_roots 2))
     (sa_ready p2_pre 2)"
  apply (rule sched_xlist_rel_ready_singletonI[
        OF frozen_p2_ready2_raw_rel,
        where p="abi_generic_list_item_ptr
          (sd_tcb_ptr frozen_p2_decode P2_RUN)" and t=P2_RUN])
  subgoal by (simp add: raw_singleton_abs_def raw_empty_abs_def
        list_insert_end_abs_def)
  subgoal by (simp add: raw_singleton_abs_def raw_empty_abs_def
        list_insert_end_abs_def)
  subgoal by (simp add: p2_pre_def p2_run_ready_def
        empty_node_ring_def list_insert_end_abs_def)
  subgoal by (simp add: p2_pre_def p2_run_ready_def
        empty_node_ring_def list_insert_end_abs_def)
  subgoal by (rule frozen_p2_run_node_decode)
  subgoal by (simp add: raw_singleton_abs_def raw_empty_abs_def p2_pre_def
        p2_run_ready_def empty_node_ring_def list_insert_end_abs_def
        frozen_p2_raw_keys_def)
  done

lemma frozen_p2_empty_sched_rel:
  assumes raw:
    "raw_xlist_rel frozen_p2_heap lp
      (raw_empty_abs frozen_p2_raw_keys)"
    and ring: "ring q = []"
    and cursor: "cursor q = None"
  shows
    "sched_xlist_rel (sd_node_decode frozen_p2_decode)
      frozen_p2_heap lp q"
  apply (rule sched_xlist_rel_emptyI[OF raw])
  using ring cursor
  by (simp_all add: raw_empty_abs_def)

lemma frozen_p2_ready1_sched_rel:
  "sched_xlist_rel (sd_node_decode frozen_p2_decode) frozen_p2_heap
     (abi_list_ptr (sr_ready generated_scheduler_roots 1))
     (sa_ready p2_pre 1)"
  apply (rule frozen_p2_empty_sched_rel[OF frozen_p2_ready1_raw_rel])
  by (simp_all add: p2_pre_def empty_node_ring_def)

lemma frozen_p2_ready3_sched_rel:
  "sched_xlist_rel (sd_node_decode frozen_p2_decode) frozen_p2_heap
     (abi_list_ptr (sr_ready generated_scheduler_roots 3))
     (sa_ready p2_pre 3)"
  apply (rule frozen_p2_empty_sched_rel[OF frozen_p2_ready3_raw_rel])
  by (simp_all add: p2_pre_def empty_node_ring_def)

lemma frozen_p2_delayed_a_sched_rel:
  "sched_xlist_rel (sd_node_decode frozen_p2_decode) frozen_p2_heap
     (abi_list_ptr (sr_delayed_a generated_scheduler_roots))
     (sa_delayed_a p2_pre)"
  apply (rule frozen_p2_empty_sched_rel[OF frozen_p2_delayed_a_raw_rel])
  by (simp_all add: p2_pre_def empty_node_ring_def)

lemma frozen_p2_delayed_b_sched_rel:
  "sched_xlist_rel (sd_node_decode frozen_p2_decode) frozen_p2_heap
     (abi_list_ptr (sr_delayed_b generated_scheduler_roots))
     (sa_delayed_b p2_pre)"
  apply (rule frozen_p2_empty_sched_rel[OF frozen_p2_delayed_b_raw_rel])
  by (simp_all add: p2_pre_def empty_node_ring_def)

lemma frozen_p2_pending_sched_rel:
  "sched_xlist_rel (sd_node_decode frozen_p2_decode) frozen_p2_heap
     (abi_list_ptr (sr_pending generated_scheduler_roots))
     (sa_pending p2_pre)"
  apply (rule frozen_p2_empty_sched_rel[OF frozen_p2_pending_raw_rel])
  by (simp_all add: p2_pre_def empty_node_ring_def)

lemma frozen_p2_suspended_sched_rel:
  "sched_xlist_rel (sd_node_decode frozen_p2_decode) frozen_p2_heap
     (abi_list_ptr (sr_suspended generated_scheduler_roots))
     (sa_suspended p2_pre)"
  apply (rule frozen_p2_empty_sched_rel[OF frozen_p2_suspended_raw_rel])
  by (simp_all add: p2_pre_def empty_node_ring_def)

lemma frozen_p2_scheduler_lists_rel:
  "scheduler_lists_rel frozen_p2_decode generated_scheduler_roots
     c p2_pre"
  if heap:
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c) = frozen_p2_heap"
proof -
  have ready:
    "\<forall>p<4.
      sched_xlist_rel (sd_node_decode frozen_p2_decode) frozen_p2_heap
        (abi_list_ptr (sr_ready generated_scheduler_roots p))
        (sa_ready p2_pre p)"
  proof (intro allI impI)
    fix p :: nat
    assume "p < 4"
    then have cases: "p = 0 \<or> p = 1 \<or> p = 2 \<or> p = 3"
      by (auto simp: less_Suc_eq)
    show
      "sched_xlist_rel (sd_node_decode frozen_p2_decode) frozen_p2_heap
        (abi_list_ptr (sr_ready generated_scheduler_roots p))
        (sa_ready p2_pre p)"
      using cases
    proof (elim disjE)
      assume "p = 0"
      then show ?thesis using frozen_p2_ready0_sched_rel by simp
    next
      assume "p = 1"
      then show ?thesis using frozen_p2_ready1_sched_rel by simp
    next
      assume "p = 2"
      then show ?thesis using frozen_p2_ready2_sched_rel by simp
    next
      assume "p = 3"
      then show ?thesis using frozen_p2_ready3_sched_rel by simp
    qed
  qed
  show ?thesis
    unfolding scheduler_lists_rel_def Let_def
    apply (simp only: heap)
    apply (intro conjI)
    subgoal by (rule ready)
    subgoal by (rule frozen_p2_delayed_a_sched_rel)
    subgoal by (rule frozen_p2_delayed_b_sched_rel)
    subgoal by (rule frozen_p2_pending_sched_rel)
    subgoal by (rule frozen_p2_suspended_sched_rel)
    done
qed


lemma frozen_p2_delayed_sentinel_max:
  "raw_sentinel_max frozen_p2_heap
      (abi_list_ptr (sr_delayed_a generated_scheduler_roots)) \<and>
   raw_sentinel_max frozen_p2_heap
      (abi_list_ptr (sr_delayed_b generated_scheduler_roots))"
  apply (intro conjI)
  subgoal using frozen_p2_heap_delayed_a
    by (simp add: raw_sentinel_max_def raw_key_at_def raw_end_item_def
        raw_sentinel_item_value_prefix_generic
        frozen_p2_empty_list_value_def)
  subgoal using frozen_p2_heap_delayed_b
    by (simp add: raw_sentinel_max_def raw_key_at_def raw_end_item_def
        raw_sentinel_item_value_prefix_generic
        frozen_p2_empty_list_value_def)
  done

lemma frozen_p2_source_footprint:
  "p2_source_footprint frozen_p2_decode generated_scheduler_roots
     frozen_p2_heap"
  using frozen_p2_static_root_geometry frozen_p2_nonheap_geometry
    frozen_p2_delayed_sentinel_max
  by (auto simp: p2_source_footprint_def)

definition frozen_p2_globals :: Scheduler_V611_Parse.globals where
  "frozen_p2_globals =
    Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_'_update
      (\<lambda>_. 0)
    (Scheduler_V611_Parse.globals.eal6_port_critical_depth_'_update
      (\<lambda>_. 0)
    (Scheduler_V611_Parse.globals.xSchedulerRunning_'_update
      (\<lambda>_. 1)
    (Scheduler_V611_Parse.globals.pxCurrentTCB_'_update
      (\<lambda>_. sd_tcb_ptr frozen_p2_decode P2_RUN)
    (Scheduler_V611_Parse.globals.eal6_port_yield_count_'_update
      (\<lambda>_. 0)
    (Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_'_update
      (\<lambda>_. 2)
    (Scheduler_V611_Parse.globals.xNumOfOverflows_'_update
      (\<lambda>_. 0)
    (Scheduler_V611_Parse.globals.uxTopReadyPriority_'_update
      (\<lambda>_. 2)
    (Scheduler_V611_Parse.globals.xMissedYield_'_update
      (\<lambda>_. 0)
    (Scheduler_V611_Parse.globals.uxMissedTicks_'_update
      (\<lambda>_. 0)
    (Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update
      (\<lambda>_. 0)
    (Scheduler_V611_Parse.globals.xTickCount_'_update
      (\<lambda>_. 5)
    (Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_'_update
      (\<lambda>_. sr_delayed_b generated_scheduler_roots)
    (Scheduler_V611_Parse.globals.pxDelayedTaskList_'_update
      (\<lambda>_. sr_delayed_a generated_scheduler_roots)
    (Scheduler_V611_Parse.globals.t_hrs_'_update
      (\<lambda>_. (frozen_p2_heap, empty_htd))
      (undefined :: Scheduler_V611_Parse.globals)))))))))))))))"

lemma frozen_p2_globals_fields [simp]:
  "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' frozen_p2_globals) =
       frozen_p2_heap \<and>
   Scheduler_V611_Parse.globals.pxDelayedTaskList_' frozen_p2_globals =
       sr_delayed_a generated_scheduler_roots \<and>
   Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_'
       frozen_p2_globals = sr_delayed_b generated_scheduler_roots \<and>
   Scheduler_V611_Parse.globals.xTickCount_' frozen_p2_globals = 5 \<and>
   Scheduler_V611_Parse.globals.uxSchedulerSuspended_' frozen_p2_globals = 0 \<and>
   Scheduler_V611_Parse.globals.uxMissedTicks_' frozen_p2_globals = 0 \<and>
   Scheduler_V611_Parse.globals.xMissedYield_' frozen_p2_globals = 0 \<and>
   Scheduler_V611_Parse.globals.uxTopReadyPriority_' frozen_p2_globals = 2 \<and>
   Scheduler_V611_Parse.globals.xNumOfOverflows_' frozen_p2_globals = 0 \<and>
   Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' frozen_p2_globals = 2 \<and>
   Scheduler_V611_Parse.globals.eal6_port_yield_count_' frozen_p2_globals = 0 \<and>
   Scheduler_V611_Parse.globals.pxCurrentTCB_' frozen_p2_globals =
       sd_tcb_ptr frozen_p2_decode P2_RUN \<and>
   Scheduler_V611_Parse.globals.xSchedulerRunning_' frozen_p2_globals = 1 \<and>
   Scheduler_V611_Parse.globals.eal6_port_critical_depth_' frozen_p2_globals = 0 \<and>
   Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_'
       frozen_p2_globals = 0"
  by (simp add: frozen_p2_globals_def hrs_mem_def)

lemma frozen_p2_roles:
  "scheduler_role_rel generated_scheduler_roots frozen_p2_globals p2_pre"
  by (simp add: scheduler_role_rel_def p2_pre_def frozen_p2_globals_def)

lemma frozen_p2_scalars:
  "scheduler_scalar_rel frozen_p2_globals p2_pre"
  by (simp add: scheduler_scalar_rel_def p2_pre_def frozen_p2_globals_def)

lemma frozen_p2_current:
  "scheduler_current_rel frozen_p2_decode frozen_p2_globals p2_pre"
  by (simp add: scheduler_current_rel_def p2_pre_def frozen_p2_globals_def)

lemma frozen_p2_boundary:
  "scheduler_boundary_rel frozen_p2_globals"
  by (simp add: scheduler_boundary_rel_def frozen_p2_globals_def)

theorem frozen_p2_endpoint:
  "scheduler_endpoint_rel StableRunning frozen_p2_decode
     generated_scheduler_roots frozen_p2_globals p2_pre"
  apply (rule p2_pre_conditional_endpointI)
  subgoal by (rule frozen_p2_decoder_rel)
  subgoal by (rule frozen_p2_scheduler_lists_rel)
    (simp add: frozen_p2_globals_def hrs_mem_def)
  subgoal by (rule frozen_p2_roles)
  subgoal by (rule frozen_p2_scalars)
  subgoal by (rule frozen_p2_current)
  subgoal by (rule frozen_p2_boundary)
  done

theorem frozen_p2_preimage_nonempty:
  "\<exists>D R c.
     scheduler_endpoint_rel StableRunning D R c p2_pre \<and>
     p2_source_footprint D R
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
  apply (intro exI[where x=frozen_p2_decode]
      exI[where x=generated_scheduler_roots]
      exI[where x=frozen_p2_globals])
  apply (intro conjI)
  subgoal by (rule frozen_p2_endpoint)
  subgoal using frozen_p2_source_footprint
    by (simp add: frozen_p2_globals_def hrs_mem_def)
  done

theorem frozen_p2_artifact_bound_vTaskDelay_2_refinement:
  "Scheduler_V611_Delay_Translation.vTaskDelay' (2 :: 32 word) \<bullet>
       frozen_p2_globals
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      scheduler_endpoint_rel YieldPending frozen_p2_decode
        generated_scheduler_roots t (task_delay_abs 2 p2_pre)
   \<rbrace>"
  by (rule scheduler_vTaskDelay_2_p2_refines_task_delay_abs[
        OF frozen_p2_endpoint])
     (simp add: frozen_p2_source_footprint frozen_p2_globals_def hrs_mem_def)

theorem frozen_p2_artifact_bound_seal:
  "\<exists>D R c.
     scheduler_endpoint_rel StableRunning D R c p2_pre \<and>
     p2_source_footprint D R
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) \<and>
     (Scheduler_V611_Delay_Translation.vTaskDelay' (2 :: 32 word) \<bullet> c
      \<lbrace>\<lambda>r t.
        r = Result () \<and>
        scheduler_endpoint_rel YieldPending D R t
          (task_delay_abs 2 p2_pre)
       \<rbrace>)"
  apply (intro exI[where x=frozen_p2_decode]
      exI[where x=generated_scheduler_roots]
      exI[where x=frozen_p2_globals])
  apply (intro conjI)
  subgoal by (rule frozen_p2_endpoint)
  subgoal using frozen_p2_source_footprint
    by (simp add: frozen_p2_globals_def hrs_mem_def)
  subgoal by (rule frozen_p2_artifact_bound_vTaskDelay_2_refinement)
  done

text \<open>
  The seal theorem is intentionally scoped to the frozen ELF-root artifact and
  the logical runtime TCB addresses above.  Compiler/linker/loader correctness,
  allocator correctness, boot reachability, and binary-code correctness are
  not consequences of this construction.
\<close>

end
