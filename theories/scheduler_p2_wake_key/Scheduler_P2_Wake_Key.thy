theory Scheduler_P2_Wake_Key
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Remove_Source.Scheduler_P2_Remove_Source"
begin

text \<open>
  The positive-delay key assignment is a nested scheduler-TCB field write,
  not an update of the old list-item key.  This transformer records that
  source operation exactly, then exposes the same byte heap as a raw-list
  whole-item update for readback and locality proofs.
\<close>

definition scheduler_generic_item_key_heap ::
  "heap_mem \<Rightarrow> Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   32 word \<Rightarrow> heap_mem"
where
  "scheduler_generic_item_key_heap h tp wake =
     heap_update (scheduler_generic_item_key_ptr tp) wake h"

lemma scheduler_generic_item_key_heap_raw_whole:
  assumes guard: "c_guard (abi_generic_list_item_ptr tp)"
  shows
    "scheduler_generic_item_key_heap h tp wake =
     heap_update (abi_generic_list_item_ptr tp)
       (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.xItemValue_C_update
         (\<lambda>_. wake)
         (h_val h (abi_generic_list_item_ptr tp))) h"
proof -
  have field:
    "scheduler_generic_item_key_heap h tp wake =
     heap_update (raw_generic_item_key_ptr tp) wake h"
    unfolding scheduler_generic_item_key_heap_def
    by (rule abi_generic_item_key_field_write)
  have whole:
    "heap_update (raw_generic_item_key_ptr tp) wake h =
     heap_update (abi_generic_list_item_ptr tp)
       (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.xItemValue_C_update
         (\<lambda>_. wake)
         (h_val h (abi_generic_list_item_ptr tp))) h"
    unfolding raw_generic_item_key_ptr_def
    by (rule
      List_V611_Raw_Skip_Translation.xLIST_ITEM_C_heap_update_fields(1)[
        OF guard])
  show ?thesis using field whole by simp
qed

lemma scheduler_generic_item_key_heap_raw_item:
  assumes guard: "c_guard (abi_generic_list_item_ptr tp)"
  shows
    "h_val (scheduler_generic_item_key_heap h tp wake)
       (abi_generic_list_item_ptr tp) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.xItemValue_C_update
       (\<lambda>_. wake) (h_val h (abi_generic_list_item_ptr tp))"
  using scheduler_generic_item_key_heap_raw_whole[OF guard]
    guard
  by (simp add: h_val_heap_update)

lemma scheduler_generic_item_key_heap_raw_key:
  assumes guard: "c_guard (abi_generic_list_item_ptr tp)"
  shows
    "raw_key_at (scheduler_generic_item_key_heap h tp wake)
       (abi_generic_list_item_ptr tp) = wake"
  using scheduler_generic_item_key_heap_raw_item[OF guard]
  by (simp add: raw_key_at_def)

lemma scheduler_generic_item_key_heap_raw_payload_frame:
  assumes guard: "c_guard (abi_generic_list_item_ptr tp)"
  shows
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxNext_C
       (h_val (scheduler_generic_item_key_heap h tp wake)
         (abi_generic_list_item_ptr tp)) =
       List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxNext_C
         (h_val h (abi_generic_list_item_ptr tp)) \<and>
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxPrevious_C
       (h_val (scheduler_generic_item_key_heap h tp wake)
         (abi_generic_list_item_ptr tp)) =
       List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxPrevious_C
         (h_val h (abi_generic_list_item_ptr tp)) \<and>
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val (scheduler_generic_item_key_heap h tp wake)
         (abi_generic_list_item_ptr tp)) =
       List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
         (h_val h (abi_generic_list_item_ptr tp)) \<and>
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
       (h_val (scheduler_generic_item_key_heap h tp wake)
         (abi_generic_list_item_ptr tp)) =
       List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
         (h_val h (abi_generic_list_item_ptr tp))"
  using scheduler_generic_item_key_heap_raw_item[OF guard]
  by simp

lemma scheduler_generic_item_key_heap_scheduler_readback:
  assumes guard: "c_guard (abi_generic_list_item_ptr tp)"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (h_val (scheduler_generic_item_key_heap h tp wake)
         (scheduler_generic_item_ptr tp)) = wake"
proof -
  have raw:
    "raw_key_at (scheduler_generic_item_key_heap h tp wake)
       (abi_generic_list_item_ptr tp) = wake"
    by (rule scheduler_generic_item_key_heap_raw_key[OF guard])
  note lens = abi_item_key_h_val[
    where h="scheduler_generic_item_key_heap h tp wake"
      and p="scheduler_generic_item_ptr tp"]
  show ?thesis using raw lens
    by (simp add: raw_key_at_def)
qed

lemma scheduler_generic_item_key_heap_scheduler_owner_frame:
  assumes guard: "c_guard (abi_generic_list_item_ptr tp)"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (scheduler_generic_item_key_heap h tp wake)
         (scheduler_generic_item_ptr tp)) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h (scheduler_generic_item_ptr tp))"
proof -
  have raw_frame:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val (scheduler_generic_item_key_heap h tp wake)
         (abi_generic_list_item_ptr tp)) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h (abi_generic_list_item_ptr tp))"
    using scheduler_generic_item_key_heap_raw_payload_frame[OF guard]
    by blast
  note after_lens = abi_item_owner_h_val[
    where h="scheduler_generic_item_key_heap h tp wake"
      and p="scheduler_generic_item_ptr tp"]
  note before_lens = abi_item_owner_h_val[
    where h=h and p="scheduler_generic_item_ptr tp"]
  show ?thesis using raw_frame after_lens before_lens by simp
qed

lemma scheduler_generic_item_key_ptr_from_item:
  "scheduler_generic_item_key_ptr tp =
   PTR(32 word)
     &((scheduler_generic_item_ptr tp)\<rightarrow>[''xItemValue_C''])"
  by (simp add: scheduler_generic_item_key_ptr_def
      scheduler_generic_item_ptr_def field_lvalue_def
      Scheduler_V611_Parse.tskTaskControlBlock_C_xGenericListItem_C_fl
      Scheduler_V611_Parse.xLIST_ITEM_C_xItemValue_C_fl)

lemma scheduler_generic_item_key_heap_scheduler_whole:
  assumes guard: "c_guard (scheduler_generic_item_ptr tp)"
  shows
    "scheduler_generic_item_key_heap h tp wake =
     heap_update (scheduler_generic_item_ptr tp)
       (Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C_update
         (\<lambda>_. wake)
         (h_val h (scheduler_generic_item_ptr tp))) h"
  unfolding scheduler_generic_item_key_heap_def
  apply (subst scheduler_generic_item_key_ptr_from_item)
  by (rule Scheduler_V611_Parse.xLIST_ITEM_C_heap_update_fields(1)[
        OF guard])

lemma scheduler_generic_item_whole_write_to_tcb:
  assumes guard: "c_guard tp"
  shows
    "heap_update (scheduler_generic_item_ptr tp) v h =
     heap_update tp
       (Scheduler_V611_Parse.tskTaskControlBlock_C.xGenericListItem_C_update
         (\<lambda>_. v) (h_val h tp)) h"
  unfolding scheduler_generic_item_ptr_def
  by (rule
    Scheduler_V611_Parse.tskTaskControlBlock_C_heap_update_fields(2)[
      OF guard])

lemma scheduler_generic_item_key_heap_priority_frame:
  assumes item_guard: "c_guard (scheduler_generic_item_ptr tp)"
    and tcb_guard: "c_guard tp"
  shows
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (scheduler_generic_item_key_heap h tp wake) tp) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C (h_val h tp)"
proof -
  have item_whole:
    "scheduler_generic_item_key_heap h tp wake =
     heap_update (scheduler_generic_item_ptr tp)
       (Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C_update
         (\<lambda>_. wake)
         (h_val h (scheduler_generic_item_ptr tp))) h"
    by (rule scheduler_generic_item_key_heap_scheduler_whole[
          OF item_guard])
  have tcb_whole:
    "heap_update (scheduler_generic_item_ptr tp)
       (Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C_update
         (\<lambda>_. wake)
         (h_val h (scheduler_generic_item_ptr tp))) h =
     heap_update tp
       (Scheduler_V611_Parse.tskTaskControlBlock_C.xGenericListItem_C_update
         (\<lambda>_.
           Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C_update
             (\<lambda>_. wake)
             (h_val h (scheduler_generic_item_ptr tp)))
         (h_val h tp)) h"
    by (rule scheduler_generic_item_whole_write_to_tcb[OF tcb_guard])
  show ?thesis
    using item_whole tcb_whole tcb_guard
    by (simp add: h_val_heap_update)
qed

lemma scheduler_generic_item_key_heap_raw_root_frame:
  assumes guard: "c_guard (abi_generic_list_item_ptr tp)"
    and disjoint:
      "raw_item_region (abi_generic_list_item_ptr tp) \<inter>
       raw_list_region lp = {}"
  shows
    "h_val (scheduler_generic_item_key_heap h tp wake) lp = h_val h lp"
  apply (subst scheduler_generic_item_key_heap_raw_whole[OF guard])
  by (rule raw_item_update_preserves_disjoint_list[OF disjoint])

lemma raw_list_update_preserves_disjoint_list:
  assumes disjoint:
    "raw_list_region lp \<inter> raw_list_region lq = {}"
  shows
    "h_val
       (heap_update lp
         (v :: List_V611_Raw_Skip_Translation.xLIST_C) h) lq =
     h_val h lq"
proof -
  have byte_disjoint:
    "{ptr_val lp..+
       length (to_bytes v
         (heap_list h
           (size_of TYPE(List_V611_Raw_Skip_Translation.xLIST_C))
           (ptr_val lp)))} \<inter>
     {ptr_val lq..+
       size_of TYPE(List_V611_Raw_Skip_Translation.xLIST_C)} = {}"
    using disjoint
    by (simp add: raw_list_region_def)
  have heap_lists_same:
    "heap_list
       (heap_update_list (ptr_val lp)
         (to_bytes v
           (heap_list h
             (size_of TYPE(List_V611_Raw_Skip_Translation.xLIST_C))
             (ptr_val lp))) h)
       (size_of TYPE(List_V611_Raw_Skip_Translation.xLIST_C))
       (ptr_val lq) =
     heap_list h
       (size_of TYPE(List_V611_Raw_Skip_Translation.xLIST_C))
       (ptr_val lq)"
    by (rule heap_list_update_disjoint_same[OF byte_disjoint])
  show ?thesis
    unfolding h_val_def heap_update_def
    using heap_lists_same by simp
qed

(* Moved to the exclusive child frame theory. *)
(*
lemma raw_remove_singleton_preserves_disjoint_list:
  assumes rel: "raw_xlist_rel h lp xs"
    and singleton: "ring xs = [p]"
    and roots:
      "raw_list_region lp \<inter> raw_list_region lq = {}"
    and item_target:
      "raw_item_region p \<inter> raw_list_region lq = {}"
  shows
    "h_val (raw_remove_concrete_heap h p) lq = h_val h lq"
proof -
  have member: "p \<in> set (ring xs)"
    using singleton by simp
  have layout: "raw_xlist_layout lp [p]"
    using rel singleton by (simp add: raw_xlist_rel_def)
  have not_end: "p \<noteq> raw_end_item lp"
    using layout by (auto simp: raw_xlist_layout_def)
  have links: "raw_ring_links h lp [p]"
    using rel singleton
    by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have singleton_links:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxPrevious_C
       (h_val h p) = raw_end_item lp \<and>
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxNext_C
       (h_val h p) = raw_end_item lp"
    using iffD1[OF raw_ring_links_singleton_iff[OF not_end] links]
    by blast
  let ?h1 = "raw_source_unlink_first h p"
  let ?h2 = "raw_source_unlink_two h p"
  let ?hi = "raw_remove_index_heap ?h2 lp p"
  let ?hc = "raw_remove_container_heap ?hi p"
  have first_field_disjoint:
    "raw_pointer_field_region
       (raw_previous_field_ptr
         (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxNext_C
           (h_val h p))) \<inter>
     raw_list_region lq = {}"
    using singleton_links
      raw_end_previous_field_region_subset_list[where lp=lp]
      roots by blast
  have h1_target: "h_val ?h1 lq = h_val h lq"
    unfolding raw_source_unlink_first_def
    by (rule raw_pointer_field_update_preserves_disjoint_list[
          OF first_field_disjoint])
  have h1_item: "h_val ?h1 p = h_val h p"
    unfolding raw_source_unlink_first_def
    by (rule raw_remove_first_unlink_preserves_item[OF rel member])
  have second_field_disjoint:
    "raw_pointer_field_region
       (raw_next_field_ptr
         (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxPrevious_C
           (h_val ?h1 p))) \<inter>
     raw_list_region lq = {}"
    using singleton_links h1_item
      raw_end_next_field_region_subset_list[where lp=lp]
      roots by blast
  have h2_target: "h_val ?h2 lq = h_val ?h1 lq"
    unfolding raw_source_unlink_two_def
    by (rule raw_pointer_field_update_preserves_disjoint_list[
          OF second_field_disjoint])
  have index_target: "h_val ?hi lq = h_val ?h2 lq"
    unfolding raw_remove_index_heap_def
    by (simp add: raw_list_update_preserves_disjoint_list[OF roots])
  have container_target: "h_val ?hc lq = h_val ?hi lq"
    unfolding raw_remove_container_heap_def
    by (rule raw_item_update_preserves_disjoint_list[OF item_target])
  have count_target:
    "h_val (raw_remove_count_heap ?hc lp) lq = h_val ?hc lq"
    unfolding raw_remove_count_heap_def
    by (rule raw_list_update_preserves_disjoint_list[OF roots])
  have concrete:
    "raw_remove_concrete_heap h p = raw_remove_source_heap h lp p"
    by (rule raw_remove_concrete_heap_eq[OF rel member])
  calc
    h_val (raw_remove_concrete_heap h p) lq =
        h_val (raw_remove_source_heap h lp p) lq
      by (simp only: concrete)
    _ = h_val (raw_remove_count_heap ?hc lp) lq
      by (simp only: raw_remove_source_heap_def raw_remove_suffix_heap_def)
    _ = h_val ?hc lq by (rule count_target)
    _ = h_val ?hi lq by (rule container_target)
    _ = h_val ?h2 lq by (rule index_target)
    _ = h_val ?h1 lq by (rule h2_target)
    _ = h_val h lq by (rule h1_target)
qed

lemma raw_xlist_rel_empty_h_val_cong:
  assumes rel: "raw_xlist_rel h lp xs"
    and empty: "ring xs = []"
    and list_same: "h_val h' lp = h_val h lp"
  shows "raw_xlist_rel h' lp xs"
  using rel empty list_same
  by (simp add: raw_xlist_rel_def raw_xlist_view_def
      raw_cursor_at_def raw_ring_links_def raw_edge_pairs_def
      raw_next_at_def raw_prev_at_def)
*)

definition p2_wake_key_heap ::
  "heap_mem \<Rightarrow> p2_tid scheduler_decode \<Rightarrow> heap_mem"
where
  "p2_wake_key_heap h D =
     scheduler_generic_item_key_heap h (sd_tcb_ptr D P2_RUN)
       ((5 :: 32 word) + 2)"

definition p2_remove_then_wake_heap ::
  "heap_mem \<Rightarrow> p2_tid scheduler_decode \<Rightarrow> heap_mem"
where
  "p2_remove_then_wake_heap h D =
     p2_wake_key_heap
       (raw_remove_concrete_heap h
         (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))) D"

lemma p2_wake_key_heap_raw_key_7:
  assumes footprint: "p2_source_footprint D R h0"
  shows
    "raw_key_at (p2_wake_key_heap h D)
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)) = 7"
proof -
  have guard:
    "c_guard (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))"
    by (rule p2_source_footprint_generic_raw_guardD[OF footprint]) simp
  show ?thesis
    unfolding p2_wake_key_heap_def
    using scheduler_generic_item_key_heap_raw_key[OF guard, where h=h]
    by simp
qed

lemma p2_wake_key_heap_scheduler_key_7:
  assumes footprint: "p2_source_footprint D R h0"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (h_val (p2_wake_key_heap h D)
         (scheduler_generic_item_ptr (sd_tcb_ptr D P2_RUN))) = 7"
proof -
  have guard:
    "c_guard (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))"
    by (rule p2_source_footprint_generic_raw_guardD[OF footprint]) simp
  show ?thesis
    unfolding p2_wake_key_heap_def
    using scheduler_generic_item_key_heap_scheduler_readback[
      OF guard, where h=h]
    by simp
qed

lemma p2_wake_key_heap_owner_frame:
  assumes footprint: "p2_source_footprint D R h0"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (p2_wake_key_heap h D)
         (scheduler_generic_item_ptr (sd_tcb_ptr D P2_RUN))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h (scheduler_generic_item_ptr (sd_tcb_ptr D P2_RUN)))"
proof -
  have guard:
    "c_guard (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))"
    by (rule p2_source_footprint_generic_raw_guardD[OF footprint]) simp
  show ?thesis
    unfolding p2_wake_key_heap_def
    using scheduler_generic_item_key_heap_scheduler_owner_frame[
      OF guard, where h=h]
    by simp
qed

lemma p2_wake_key_heap_priority_frame:
  assumes footprint: "p2_source_footprint D R h0"
  shows
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (p2_wake_key_heap h D) (sd_tcb_ptr D P2_RUN)) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val h (sd_tcb_ptr D P2_RUN))"
proof -
  note guards = p2_source_footprint_run_guardsD[OF footprint]
  have tcb_guard: "c_guard (sd_tcb_ptr D P2_RUN)"
    using guards by blast
  have item_guard:
    "c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D P2_RUN))"
    using guards by blast
  show ?thesis
    unfolding p2_wake_key_heap_def
    by (rule scheduler_generic_item_key_heap_priority_frame[
          OF item_guard tcb_guard])
qed

lemma p2_wake_key_heap_raw_root_frame:
  assumes footprint: "p2_source_footprint D R h0"
    and root: "lp \<in> set (p2_physical_roots R)"
  shows
    "h_val (p2_wake_key_heap h D) (abi_list_ptr lp) =
     h_val h (abi_list_ptr lp)"
proof -
  have guard:
    "c_guard (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))"
    by (rule p2_source_footprint_generic_raw_guardD[OF footprint]) simp
  have disjoint:
    "raw_item_region
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)) \<inter>
     raw_list_region (abi_list_ptr lp) = {}"
    by (rule p2_source_footprint_generic_item_root_disjointD[
          OF footprint _ root]) simp
  show ?thesis
    unfolding p2_wake_key_heap_def
    by (rule scheduler_generic_item_key_heap_raw_root_frame[
          OF guard disjoint])
qed

lemma p2_wake_key_heap_all_raw_roots_frame:
  assumes footprint: "p2_source_footprint D R h0"
  shows
    "\<forall>lp \<in> set (p2_physical_roots R).
       h_val (p2_wake_key_heap h D) (abi_list_ptr lp) =
       h_val h (abi_list_ptr lp)"
  using p2_wake_key_heap_raw_root_frame[OF footprint] by blast

lemma p2_wake_key_heap_raw_sentinel_fields_frame:
  assumes footprint: "p2_source_footprint D R h0"
    and root: "lp \<in> set (p2_physical_roots R)"
  shows
    "List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.xItemValue_C
       (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
         (h_val (p2_wake_key_heap h D) (abi_list_ptr lp))) =
       List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.xItemValue_C
         (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
           (h_val h (abi_list_ptr lp))) \<and>
     List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxNext_C
       (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
         (h_val (p2_wake_key_heap h D) (abi_list_ptr lp))) =
       List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxNext_C
         (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
           (h_val h (abi_list_ptr lp))) \<and>
     List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxPrevious_C
       (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
         (h_val (p2_wake_key_heap h D) (abi_list_ptr lp))) =
       List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxPrevious_C
         (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
           (h_val h (abi_list_ptr lp)))"
  using p2_wake_key_heap_raw_root_frame[OF footprint root]
  by simp

lemma p2_wake_key_heap_sentinel_max_frame:
  assumes footprint: "p2_source_footprint D R h0"
    and root: "lp \<in> set (p2_physical_roots R)"
    and sentinel: "raw_sentinel_max h (abi_list_ptr lp)"
  shows "raw_sentinel_max (p2_wake_key_heap h D) (abi_list_ptr lp)"
proof -
  have list_same:
    "h_val (p2_wake_key_heap h D) (abi_list_ptr lp) =
     h_val h (abi_list_ptr lp)"
    by (rule p2_wake_key_heap_raw_root_frame[OF footprint root])
  have key_same:
    "raw_key_at (p2_wake_key_heap h D)
       (raw_end_item (abi_list_ptr lp)) =
     raw_key_at h (raw_end_item (abi_list_ptr lp))"
    by (rule raw_ordered_sentinel_key_cong[OF list_same])
  show ?thesis
    using sentinel key_same by (simp add: raw_sentinel_max_def)
qed

lemma p2_wake_key_heap_footprint:
  assumes footprint: "p2_source_footprint D R h"
  shows "p2_source_footprint D R (p2_wake_key_heap h D)"
proof -
  have delayed_a_root:
    "sr_delayed_a R \<in> set (p2_physical_roots R)"
    by (simp add: p2_physical_roots_def)
  have delayed_b_root:
    "sr_delayed_b R \<in> set (p2_physical_roots R)"
    by (simp add: p2_physical_roots_def)
  have old_max:
    "raw_sentinel_max h (abi_list_ptr (sr_delayed_a R)) \<and>
     raw_sentinel_max h (abi_list_ptr (sr_delayed_b R))"
    by (rule p2_source_footprint_delayed_sentinel_maxD[OF footprint])
  have delayed_a_max:
    "raw_sentinel_max (p2_wake_key_heap h D)
       (abi_list_ptr (sr_delayed_a R))"
    by (rule p2_wake_key_heap_sentinel_max_frame[
          OF footprint delayed_a_root])
       (use old_max in blast)
  have delayed_b_max:
    "raw_sentinel_max (p2_wake_key_heap h D)
       (abi_list_ptr (sr_delayed_b R))"
    by (rule p2_wake_key_heap_sentinel_max_frame[
          OF footprint delayed_b_root])
       (use old_max in blast)
  show ?thesis
    using footprint delayed_a_max delayed_b_max
    unfolding p2_source_footprint_def by blast
qed

(* Diagnostic boundary: temporarily exclude its dependent P2 bundle. *)
(*
lemma p2_remove_then_wake_delayed_a_ordered_emptyE:
  fixes s :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R s p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))"
  obtains rx where
    "raw_xlist_rel
       (p2_remove_then_wake_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)) D)
       (abi_list_ptr (sr_delayed_a R)) rx"
    "ring rx = []"
    "cursor rx = None"
    "raw_sentinel_max
       (p2_remove_then_wake_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)) D)
       (abi_list_ptr (sr_delayed_a R))"
    "raw_fresh_for_insert
       (abi_list_ptr (sr_delayed_a R)) (ring rx)
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))"
    "raw_key_at
       (p2_remove_then_wake_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)) D)
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)) = 7"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)"
  let ?ready = "abi_list_ptr (sr_ready R 2)"
  let ?delayed = "abi_list_ptr (sr_delayed_a R)"
  let ?p = "abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)"
  let ?hr = "raw_remove_concrete_heap ?h ?p"
  let ?hk = "p2_wake_key_heap ?hr D"
  from p2_pre_ready2_raw_singletonE[OF decode lists]
  obtain ready_xs where
      ready_rel: "raw_xlist_rel ?h ?ready ready_xs"
    and ready_ring: "ring ready_xs = [?p]"
    and ready_cursor: "cursor ready_xs = Some ?p" .
  from p2_pre_delayed_a_ordered_emptyE[OF lists footprint]
  obtain rx where
      delayed_rel: "raw_xlist_rel ?h ?delayed rx"
    and empty: "ring rx = []"
    and cursor: "cursor rx = None"
    and sentinel: "raw_sentinel_max ?h ?delayed"
    and fresh:
      "raw_fresh_for_insert ?delayed (ring rx) ?p" .
  have ready_root: "sr_ready R 2 \<in> set (p2_physical_roots R)"
    by (simp add: p2_physical_roots_def)
  have delayed_root:
    "sr_delayed_a R \<in> set (p2_physical_roots R)"
    by (simp add: p2_physical_roots_def)
  have roots_distinct: "sr_ready R 2 \<noteq> sr_delayed_a R"
    using footprint
    by (auto simp: p2_source_footprint_def p2_physical_roots_def)
  have roots_disjoint:
    "raw_list_region ?ready \<inter> raw_list_region ?delayed = {}"
    by (rule p2_source_footprint_raw_roots_disjointD[
          OF footprint ready_root delayed_root roots_distinct])
  have item_delayed_disjoint:
    "raw_item_region ?p \<inter> raw_list_region ?delayed = {}"
    by (rule p2_source_footprint_generic_item_root_disjointD[
          OF footprint _ delayed_root]) simp
  have remove_delayed:
    "h_val ?hr ?delayed = h_val ?h ?delayed"
    by (rule raw_remove_singleton_preserves_disjoint_list[
          OF ready_rel ready_ring roots_disjoint item_delayed_disjoint])
  have key_delayed:
    "h_val ?hk ?delayed = h_val ?hr ?delayed"
    unfolding p2_remove_then_wake_heap_def
    by (rule p2_wake_key_heap_raw_root_frame[
          OF footprint delayed_root])
  have final_delayed:
    "h_val ?hk ?delayed = h_val ?h ?delayed"
    using remove_delayed key_delayed by simp
  have final_rel: "raw_xlist_rel ?hk ?delayed rx"
    by (rule raw_xlist_rel_empty_h_val_cong[
          OF delayed_rel empty final_delayed])
  have sentinel_key_same:
    "raw_key_at ?hk (raw_end_item ?delayed) =
     raw_key_at ?h (raw_end_item ?delayed)"
    by (rule raw_ordered_sentinel_key_cong[OF final_delayed])
  have final_sentinel: "raw_sentinel_max ?hk ?delayed"
    using sentinel sentinel_key_same
    by (simp add: raw_sentinel_max_def)
  have final_key: "raw_key_at ?hk ?p = 7"
    by (rule p2_wake_key_heap_raw_key_7[OF footprint])
  show ?thesis
    unfolding p2_remove_then_wake_heap_def
    by (rule that[OF final_rel empty cursor final_sentinel fresh final_key])
qed
*)

end
