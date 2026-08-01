theory List_V611_Raw_R6_Remove_Metadata
  imports "EAL6_FreeRTOS_V611_List_Raw_R6_Unlink_Projection.List_V611_Raw_R6_Unlink_Projection"
begin

text \<open>
  Pure cursor transfer for removal.  It mirrors the source branch
  `if pxIndex == p then pxIndex = p->pxPrevious` and converts the embedded
  sentinel back to the abstract None cursor.  No heap update is opened here.
\<close>

definition raw_count_field_ptr :: "xLIST_C ptr \<Rightarrow> 32 word ptr"
where
  "raw_count_field_ptr lp =
     PTR(32 word) &(lp\<rightarrow>[''uxNumberOfItems_C''])"

definition raw_count_field_region :: "xLIST_C ptr \<Rightarrow> addr set"
where
  "raw_count_field_region lp =
     {ptr_val (raw_count_field_ptr lp)..+size_of TYPE(32 word)}"

lemma raw_count_field_region_subset_list:
  "raw_count_field_region lp \<subseteq> raw_list_region lp"
  unfolding raw_count_field_region_def raw_count_field_ptr_def
    raw_list_region_def
  by (auto simp: field_lvalue_def xLIST_C_uxNumberOfItems_C_fl
      size_of_def intvl_def)

lemma raw_end_next_field_disjoint_count:
  "raw_pointer_field_region
      (raw_next_field_ptr (raw_end_item lp)) \<inter>
   raw_count_field_region lp = {}"
proof -
  have offsets:
    "{(12 :: addr)..+4} \<inter> {(0 :: addr)..+4} = {}"
  proof -
    have "{(0 :: addr)..+4} \<inter> {(12 :: addr)..+4} = {}"
      apply (rule intvl_disj_left)
      apply simp
      by (simp add: addr_card_def card_word)
    then show ?thesis by (simp add: Int_commute)
  qed
  have shifted:
    "{ptr_val lp + (12 :: addr)..+4} \<inter>
     {ptr_val lp + (0 :: addr)..+4} = {}"
    apply (subst intvl_disj_offset)
    by (rule offsets)
  show ?thesis
    using shifted
    by (simp add: raw_pointer_field_region_def raw_next_field_ptr_def
        raw_count_field_region_def raw_count_field_ptr_def raw_end_item_def
        raw_sentinel_ptr_def field_lvalue_def xLIST_ITEM_C_pxNext_C_fl
        xLIST_C_xListEnd_C_fl xLIST_C_uxNumberOfItems_C_fl size_of_def
        add.commute)
qed

lemma raw_end_previous_field_disjoint_count:
  "raw_pointer_field_region
      (raw_previous_field_ptr (raw_end_item lp)) \<inter>
   raw_count_field_region lp = {}"
proof -
  have offsets:
    "{(16 :: addr)..+4} \<inter> {(0 :: addr)..+4} = {}"
  proof -
    have "{(0 :: addr)..+4} \<inter> {(16 :: addr)..+4} = {}"
      apply (rule intvl_disj_left)
      apply simp
      by (simp add: addr_card_def card_word)
    then show ?thesis by (simp add: Int_commute)
  qed
  have shifted:
    "{ptr_val lp + (16 :: addr)..+4} \<inter>
     {ptr_val lp + (0 :: addr)..+4} = {}"
    apply (subst intvl_disj_offset)
    by (rule offsets)
  show ?thesis
    using shifted
    by (simp add: raw_pointer_field_region_def raw_previous_field_ptr_def
        raw_count_field_region_def raw_count_field_ptr_def raw_end_item_def
        raw_sentinel_ptr_def field_lvalue_def
        xLIST_ITEM_C_pxPrevious_C_fl xLIST_C_xListEnd_C_fl
        xLIST_C_uxNumberOfItems_C_fl size_of_def add.commute)
qed

lemma raw_cycle_next_field_disjoint_count:
  assumes layout: "raw_xlist_layout lp rs"
    and member: "u \<in> insert (raw_end_item lp) (set rs)"
  shows
    "raw_pointer_field_region (raw_next_field_ptr u) \<inter>
     raw_count_field_region lp = {}"
proof (cases "u = raw_end_item lp")
  case True
  show ?thesis using True raw_end_next_field_disjoint_count by simp
next
  case False
  have u_real: "u \<in> set rs" using member False by simp
  have item_list:
    "raw_item_region u \<inter> raw_list_region lp = {}"
    using layout u_real by (auto simp: raw_xlist_layout_def)
  show ?thesis
    using raw_next_field_region_subset_item[where u=u]
      raw_count_field_region_subset_list[where lp=lp] item_list
    by blast
qed

lemma raw_cycle_previous_field_disjoint_count:
  assumes layout: "raw_xlist_layout lp rs"
    and member: "u \<in> insert (raw_end_item lp) (set rs)"
  shows
    "raw_pointer_field_region (raw_previous_field_ptr u) \<inter>
     raw_count_field_region lp = {}"
proof (cases "u = raw_end_item lp")
  case True
  show ?thesis using True raw_end_previous_field_disjoint_count by simp
next
  case False
  have u_real: "u \<in> set rs" using member False by simp
  have item_list:
    "raw_item_region u \<inter> raw_list_region lp = {}"
    using layout u_real by (auto simp: raw_xlist_layout_def)
  show ?thesis
    using raw_previous_field_region_subset_item[where u=u]
      raw_count_field_region_subset_list[where lp=lp] item_list
    by blast
qed

lemma raw_pointer_update_preserves_disjoint_count_field:
  assumes disjoint:
    "raw_pointer_field_region f \<inter> raw_count_field_region lp = {}"
  shows
    "h_val (heap_update f (q :: raw_node_id) h)
       (raw_count_field_ptr lp) =
     h_val h (raw_count_field_ptr lp)"
proof -
  have byte_disjoint:
    "{ptr_val f..+
       length (to_bytes q
         (heap_list h (size_of TYPE(raw_node_id)) (ptr_val f)))} \<inter>
     {ptr_val (raw_count_field_ptr lp)..+size_of TYPE(32 word)} = {}"
    using disjoint
    by (simp add: raw_pointer_field_region_def raw_count_field_region_def)
  have heap_lists_same:
    "heap_list
       (heap_update_list (ptr_val f)
         (to_bytes q
           (heap_list h (size_of TYPE(raw_node_id)) (ptr_val f))) h)
       (size_of TYPE(32 word)) (ptr_val (raw_count_field_ptr lp)) =
     heap_list h (size_of TYPE(32 word))
       (ptr_val (raw_count_field_ptr lp))"
    by (rule heap_list_update_disjoint_same[OF byte_disjoint])
  show ?thesis
    unfolding h_val_def heap_update_def
    using heap_lists_same by simp
qed

lemma raw_count_field_value:
  "h_val h (raw_count_field_ptr lp) =
   uxNumberOfItems_C (h_val h lp)"
  unfolding raw_count_field_ptr_def
  by (rule xLIST_C_h_val_fields(1))

lemma raw_next_field_update_preserves_count:
  assumes layout: "raw_xlist_layout lp rs"
    and member: "u \<in> insert (raw_end_item lp) (set rs)"
  shows
    "uxNumberOfItems_C
       (h_val (heap_update (raw_next_field_ptr u) q h) lp) =
     uxNumberOfItems_C (h_val h lp)"
proof -
  have field_same:
    "h_val (heap_update (raw_next_field_ptr u) q h)
       (raw_count_field_ptr lp) =
     h_val h (raw_count_field_ptr lp)"
    by (rule raw_pointer_update_preserves_disjoint_count_field[
          OF raw_cycle_next_field_disjoint_count[OF layout member]])
  show ?thesis
    using raw_count_field_value[
        where h="heap_update (raw_next_field_ptr u) q h" and lp=lp]
      raw_count_field_value[where h=h and lp=lp] field_same
    by simp
qed

lemma raw_previous_field_update_preserves_count:
  assumes layout: "raw_xlist_layout lp rs"
    and member: "u \<in> insert (raw_end_item lp) (set rs)"
  shows
    "uxNumberOfItems_C
       (h_val (heap_update (raw_previous_field_ptr u) q h) lp) =
     uxNumberOfItems_C (h_val h lp)"
proof -
  have field_same:
    "h_val (heap_update (raw_previous_field_ptr u) q h)
       (raw_count_field_ptr lp) =
     h_val h (raw_count_field_ptr lp)"
    by (rule raw_pointer_update_preserves_disjoint_count_field[
          OF raw_cycle_previous_field_disjoint_count[OF layout member]])
  show ?thesis
    using raw_count_field_value[
        where h="heap_update (raw_previous_field_ptr u) q h" and lp=lp]
      raw_count_field_value[where h=h and lp=lp] field_same
    by simp
qed

lemma raw_unlink_two_preserves_count:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "uxNumberOfItems_C (h_val (raw_unlink_two h lp p) lp) =
     uxNumberOfItems_C (h_val h lp)"
proof -
  let ?cycle = "insert (raw_end_item lp) (set (ring xs))"
  let ?a = "raw_prev_at h lp p"
  let ?b = "raw_next_at h lp p"
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have p_cycle: "p \<in> ?cycle" using member by simp
  have a_cycle: "?a \<in> ?cycle"
    by (rule raw_ring_links_prev_closed[OF links p_cycle])
  have b_cycle: "?b \<in> ?cycle"
    by (rule raw_ring_links_next_closed[OF links p_cycle])
  have first:
    "uxNumberOfItems_C (h_val (raw_unlink_first h lp p) lp) =
     uxNumberOfItems_C (h_val h lp)"
    unfolding raw_unlink_first_def
    by (rule raw_previous_field_update_preserves_count[
          OF layout b_cycle])
  have second:
    "uxNumberOfItems_C (h_val (raw_unlink_two h lp p) lp) =
     uxNumberOfItems_C (h_val (raw_unlink_first h lp p) lp)"
    unfolding raw_unlink_two_def
    by (rule raw_next_field_update_preserves_count[OF layout a_cycle])
  show ?thesis using first second by simp
qed

definition raw_source_unlink_first ::
  "heap_mem \<Rightarrow> raw_node_id \<Rightarrow> heap_mem"
where
  "raw_source_unlink_first h p =
     heap_update
       (raw_previous_field_ptr
         (xLIST_ITEM_C.pxNext_C (h_val h p)))
       (xLIST_ITEM_C.pxPrevious_C (h_val h p)) h"

definition raw_source_unlink_two ::
  "heap_mem \<Rightarrow> raw_node_id \<Rightarrow> heap_mem"
where
  "raw_source_unlink_two h p =
     heap_update
       (raw_next_field_ptr
         (xLIST_ITEM_C.pxPrevious_C
           (h_val (raw_source_unlink_first h p) p)))
       (xLIST_ITEM_C.pxNext_C
         (h_val (raw_source_unlink_first h p) p))
       (raw_source_unlink_first h p)"

lemma raw_source_unlink_first_eq:
  "raw_source_unlink_first h p = raw_unlink_first h lp p"
  unfolding raw_source_unlink_first_def raw_unlink_first_def
  using raw_full_next_is_sentinel_safe[where h=h and u=p and lp=lp]
    raw_full_previous_is_sentinel_safe[where h=h and u=p and lp=lp]
  by simp

lemma raw_source_unlink_two_eq:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows "raw_source_unlink_two h p = raw_unlink_two h lp p"
proof -
  let ?h1 = "raw_source_unlink_first h p"
  have first_eq: "?h1 = raw_unlink_first h lp p"
    by (rule raw_source_unlink_first_eq)
  have item_same: "h_val ?h1 p = h_val h p"
    unfolding raw_source_unlink_first_def
    by (rule raw_remove_first_unlink_preserves_item[OF rel member])
  have next_eq:
    "xLIST_ITEM_C.pxNext_C (h_val h p) = raw_next_at h lp p"
    by (rule raw_full_next_is_sentinel_safe)
  have previous_eq:
    "xLIST_ITEM_C.pxPrevious_C (h_val h p) = raw_prev_at h lp p"
    by (rule raw_full_previous_is_sentinel_safe)
  show ?thesis
    unfolding raw_source_unlink_two_def raw_unlink_two_def
    using first_eq item_same next_eq previous_eq by simp
qed

lemma raw_source_unlink_two_item_same:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows "h_val (raw_source_unlink_two h p) p = h_val h p"
  using raw_remove_two_unlink_writes_preserve_item[OF rel member]
  by (simp add: raw_source_unlink_two_def raw_source_unlink_first_def Let_def)

lemma raw_source_unlink_two_container_cast:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "PTR_COERCE(unit \<rightarrow> xLIST_C)
       (pvContainer_C (h_val (raw_source_unlink_two h p) p)) = lp"
proof -
  have item_same:
    "h_val (raw_source_unlink_two h p) p = h_val h p"
    by (rule raw_source_unlink_two_item_same[OF rel member])
  have container:
    "pvContainer_C (h_val h p) =
     PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    using raw_xlist_rel_live_itemD[OF rel member] by blast
  show ?thesis using item_same container by simp
qed

lemma raw_source_unlink_two_preserves_count:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "uxNumberOfItems_C (h_val (raw_source_unlink_two h p) lp) =
     uxNumberOfItems_C (h_val h lp)"
  using raw_source_unlink_two_eq[OF rel member]
    raw_unlink_two_preserves_count[OF rel member]
  by simp

definition raw_remove_index_heap ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow> heap_mem"
where
  "raw_remove_index_heap h lp p =
     (if pxIndex_C (h_val h lp) = p
      then heap_update lp
        (pxIndex_C_update
          (\<lambda>_. xLIST_ITEM_C.pxPrevious_C (h_val h p))
          (h_val h lp)) h
      else h)"

definition raw_remove_container_heap ::
  "heap_mem \<Rightarrow> raw_node_id \<Rightarrow> heap_mem"
where
  "raw_remove_container_heap h p =
     heap_update p
       (pvContainer_C_update (\<lambda>_. NULL) (h_val h p)) h"

definition raw_remove_count_heap ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> heap_mem"
where
  "raw_remove_count_heap h lp =
     heap_update lp
       (uxNumberOfItems_C_update (\<lambda>n. n - 1) (h_val h lp)) h"

definition raw_remove_suffix_heap ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow> heap_mem"
where
  "raw_remove_suffix_heap h lp p =
     raw_remove_count_heap
       (raw_remove_container_heap (raw_remove_index_heap h lp p) p) lp"

lemma raw_remove_index_heap_preserves_count:
  assumes guard: "c_guard lp"
  shows
    "uxNumberOfItems_C (h_val (raw_remove_index_heap h lp p) lp) =
     uxNumberOfItems_C (h_val h lp)"
  unfolding raw_remove_index_heap_def
  using guard by (simp add: h_val_heap_update)

lemma raw_remove_container_heap_preserves_list:
  assumes disjoint:
    "raw_item_region p \<inter> raw_list_region lp = {}"
  shows
    "h_val (raw_remove_container_heap h p) lp = h_val h lp"
  unfolding raw_remove_container_heap_def
  by (rule raw_item_update_preserves_disjoint_list[OF disjoint])

lemma raw_remove_count_heap_readback:
  assumes guard: "c_guard lp"
  shows
    "uxNumberOfItems_C (h_val (raw_remove_count_heap h lp) lp) =
     uxNumberOfItems_C (h_val h lp) - 1"
  unfolding raw_remove_count_heap_def
  using guard by (simp add: h_val_heap_update)

lemma raw_remove_suffix_count_effect:
  assumes layout: "raw_xlist_layout lp rs"
    and member: "p \<in> set rs"
  shows
    "uxNumberOfItems_C
       (h_val (raw_remove_suffix_heap h lp p) lp) =
     uxNumberOfItems_C (h_val h lp) - 1"
proof -
  let ?hi = "raw_remove_index_heap h lp p"
  let ?hc = "raw_remove_container_heap ?hi p"
  have guard: "c_guard lp"
    using layout by (simp add: raw_xlist_layout_def)
  have disjoint:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using layout member by (auto simp: raw_xlist_layout_def)
  have index_count:
    "uxNumberOfItems_C (h_val ?hi lp) =
     uxNumberOfItems_C (h_val h lp)"
    by (rule raw_remove_index_heap_preserves_count[OF guard])
  have container_list: "h_val ?hc lp = h_val ?hi lp"
    by (rule raw_remove_container_heap_preserves_list[OF disjoint])
  have final_count:
    "uxNumberOfItems_C (h_val (raw_remove_count_heap ?hc lp) lp) =
     uxNumberOfItems_C (h_val ?hc lp) - 1"
    by (rule raw_remove_count_heap_readback[OF guard])
  show ?thesis
    using index_count container_list final_count
    by (simp add: raw_remove_suffix_heap_def)
qed

definition raw_remove_taken_index_heap ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow> heap_mem"
where
  "raw_remove_taken_index_heap h lp p =
     heap_update lp
       (pxIndex_C_update
         (\<lambda>_. xLIST_ITEM_C.pxPrevious_C (h_val h p))
         (h_val h lp)) h"

definition raw_remove_taken_suffix_heap ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow> heap_mem"
where
  "raw_remove_taken_suffix_heap h lp p =
     raw_remove_count_heap
       (raw_remove_container_heap
         (raw_remove_taken_index_heap h lp p) p) lp"

definition raw_remove_plain_suffix_heap ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow> heap_mem"
where
  "raw_remove_plain_suffix_heap h lp p =
     raw_remove_count_heap (raw_remove_container_heap h p) lp"

lemma raw_remove_taken_index_heap_preserves_count:
  assumes guard: "c_guard lp"
  shows
    "uxNumberOfItems_C
       (h_val (raw_remove_taken_index_heap h lp p) lp) =
     uxNumberOfItems_C (h_val h lp)"
  unfolding raw_remove_taken_index_heap_def
  using guard by (simp add: h_val_heap_update)

lemma raw_remove_taken_suffix_count_effect:
  assumes layout: "raw_xlist_layout lp rs"
    and member: "p \<in> set rs"
  shows
    "uxNumberOfItems_C
       (h_val (raw_remove_taken_suffix_heap h lp p) lp) =
     uxNumberOfItems_C (h_val h lp) - 1"
proof -
  let ?hi = "raw_remove_taken_index_heap h lp p"
  let ?hc = "raw_remove_container_heap ?hi p"
  have guard: "c_guard lp"
    using layout by (simp add: raw_xlist_layout_def)
  have disjoint:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using layout member by (auto simp: raw_xlist_layout_def)
  have index_count:
    "uxNumberOfItems_C (h_val ?hi lp) =
     uxNumberOfItems_C (h_val h lp)"
    by (rule raw_remove_taken_index_heap_preserves_count[OF guard])
  have container_list: "h_val ?hc lp = h_val ?hi lp"
    by (rule raw_remove_container_heap_preserves_list[OF disjoint])
  have final_count:
    "uxNumberOfItems_C (h_val (raw_remove_count_heap ?hc lp) lp) =
     uxNumberOfItems_C (h_val ?hc lp) - 1"
    by (rule raw_remove_count_heap_readback[OF guard])
  show ?thesis
    using index_count container_list final_count
    by (simp add: raw_remove_taken_suffix_heap_def)
qed

lemma raw_remove_plain_suffix_count_effect:
  assumes layout: "raw_xlist_layout lp rs"
    and member: "p \<in> set rs"
  shows
    "uxNumberOfItems_C
       (h_val (raw_remove_plain_suffix_heap h lp p) lp) =
     uxNumberOfItems_C (h_val h lp) - 1"
proof -
  let ?hc = "raw_remove_container_heap h p"
  have guard: "c_guard lp"
    using layout by (simp add: raw_xlist_layout_def)
  have disjoint:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using layout member by (auto simp: raw_xlist_layout_def)
  have container_list: "h_val ?hc lp = h_val h lp"
    by (rule raw_remove_container_heap_preserves_list[OF disjoint])
  have final_count:
    "uxNumberOfItems_C (h_val (raw_remove_count_heap ?hc lp) lp) =
     uxNumberOfItems_C (h_val ?hc lp) - 1"
    by (rule raw_remove_count_heap_readback[OF guard])
  show ?thesis
    using container_list final_count
    by (simp add: raw_remove_plain_suffix_heap_def)
qed

definition raw_remove_source_heap ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow> heap_mem"
where
  "raw_remove_source_heap h lp p =
     raw_remove_suffix_heap (raw_source_unlink_two h p) lp p"

definition raw_remove_concrete_heap ::
  "heap_mem \<Rightarrow> raw_node_id \<Rightarrow> heap_mem"
where
  "raw_remove_concrete_heap h p =
     (let hu = raw_source_unlink_two h p;
          lp = PTR_COERCE(unit \<rightarrow> xLIST_C)
            (pvContainer_C (h_val hu p))
      in raw_remove_suffix_heap hu lp p)"

lemma raw_remove_concrete_heap_eq:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_remove_concrete_heap h p = raw_remove_source_heap h lp p"
  using raw_source_unlink_two_container_cast[OF rel member]
  by (simp add: raw_remove_concrete_heap_def raw_remove_source_heap_def)

lemma raw_remove_source_heap_count_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "uxNumberOfItems_C (h_val (raw_remove_source_heap h lp p) lp) =
     uxNumberOfItems_C (h_val h lp) - 1"
proof -
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have suffix:
    "uxNumberOfItems_C
       (h_val
         (raw_remove_suffix_heap (raw_source_unlink_two h p) lp p) lp) =
     uxNumberOfItems_C (h_val (raw_source_unlink_two h p) lp) - 1"
    by (rule raw_remove_suffix_count_effect[OF layout member])
  have unlink:
    "uxNumberOfItems_C (h_val (raw_source_unlink_two h p) lp) =
     uxNumberOfItems_C (h_val h lp)"
    by (rule raw_source_unlink_two_preserves_count[OF rel member])
  show ?thesis
    using suffix unlink by (simp add: raw_remove_source_heap_def)
qed

lemma raw_remove_concrete_heap_count_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "uxNumberOfItems_C (h_val (raw_remove_concrete_heap h p) lp) =
     uxNumberOfItems_C (h_val h lp) - 1"
  using raw_remove_concrete_heap_eq[OF rel member]
    raw_remove_source_heap_count_effect[OF rel member]
  by simp

lemma raw_remove_taken_source_count_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "uxNumberOfItems_C
       (h_val
         (raw_remove_taken_suffix_heap (raw_source_unlink_two h p) lp p)
         lp) =
     uxNumberOfItems_C (h_val h lp) - 1"
proof -
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have suffix:
    "uxNumberOfItems_C
       (h_val
         (raw_remove_taken_suffix_heap (raw_source_unlink_two h p) lp p)
         lp) =
     uxNumberOfItems_C (h_val (raw_source_unlink_two h p) lp) - 1"
    by (rule raw_remove_taken_suffix_count_effect[OF layout member])
  have unlink:
    "uxNumberOfItems_C (h_val (raw_source_unlink_two h p) lp) =
     uxNumberOfItems_C (h_val h lp)"
    by (rule raw_source_unlink_two_preserves_count[OF rel member])
  show ?thesis using suffix unlink by simp
qed

lemma raw_remove_plain_source_count_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "uxNumberOfItems_C
       (h_val
         (raw_remove_plain_suffix_heap (raw_source_unlink_two h p) lp p)
         lp) =
     uxNumberOfItems_C (h_val h lp) - 1"
proof -
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have suffix:
    "uxNumberOfItems_C
       (h_val
         (raw_remove_plain_suffix_heap (raw_source_unlink_two h p) lp p)
         lp) =
     uxNumberOfItems_C (h_val (raw_source_unlink_two h p) lp) - 1"
    by (rule raw_remove_plain_suffix_count_effect[OF layout member])
  have unlink:
    "uxNumberOfItems_C (h_val (raw_source_unlink_two h p) lp) =
     uxNumberOfItems_C (h_val h lp)"
    by (rule raw_source_unlink_two_preserves_count[OF rel member])
  show ?thesis using suffix unlink by simp
qed

lemma raw_xlist_remove_cursor_transfer:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
    and index_post:
      "pxIndex_C (h_val h' lp) =
       (if pxIndex_C (h_val h lp) = p
        then raw_prev_at h lp p
        else pxIndex_C (h_val h lp))"
  shows
    "raw_cursor_at h' lp = cursor (list_remove_abs p xs)"
proof -
  have index_cursor:
    "pxIndex_C (h_val h lp) = raw_cursor_node lp xs"
    by (rule raw_xlist_rel_index_eq_cursor_node[OF rel])
  have wf: "xlist_wf xs"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have p_not_end: "p \<noteq> raw_end_item lp"
    using layout member by (auto simp: raw_xlist_layout_def)
  show ?thesis
  proof (cases "cursor xs")
    case None
    have old_index: "pxIndex_C (h_val h lp) = raw_end_item lp"
      using index_cursor None by (simp add: raw_cursor_node_def)
    have final_index: "pxIndex_C (h_val h' lp) = raw_end_item lp"
      using index_post old_index p_not_end by simp
    show ?thesis
      using None final_index
      by (simp add: raw_cursor_at_def list_remove_abs_def)
  next
    case (Some c)
    have cursor_some: "cursor xs = Some c" by (rule Some)
    have c_member: "c \<in> set (ring xs)"
      using wf cursor_some by (auto simp: xlist_wf_def)
    have c_not_end: "c \<noteq> raw_end_item lp"
      using layout c_member by (auto simp: raw_xlist_layout_def)
    have old_index: "pxIndex_C (h_val h lp) = c"
      using index_cursor cursor_some by (simp add: raw_cursor_node_def)
    show ?thesis
    proof (cases "c = p")
      case True
      have previous:
        "raw_prev_at h lp p =
         (case predecessor p (ring xs) of
            None \<Rightarrow> raw_end_item lp
          | Some q \<Rightarrow> q)"
        by (rule raw_xlist_rel_member_previous[OF rel member])
      have final_index:
        "pxIndex_C (h_val h' lp) =
         (case predecessor p (ring xs) of
            None \<Rightarrow> raw_end_item lp
          | Some q \<Rightarrow> q)"
        using index_post old_index True previous by simp
      show ?thesis
      proof (cases "predecessor p (ring xs)")
        case None
        show ?thesis
          using cursor_some True final_index None
          by (simp add: raw_cursor_at_def list_remove_abs_def)
      next
        case (Some q)
        have q_member: "q \<in> set (ring xs)"
          by (rule predecessor_member[OF Some])
        have q_not_end: "q \<noteq> raw_end_item lp"
          using layout q_member by (auto simp: raw_xlist_layout_def)
        show ?thesis
          using cursor_some True final_index Some q_not_end
          by (simp add: raw_cursor_at_def list_remove_abs_def)
      qed
    next
      case False
      have final_index: "pxIndex_C (h_val h' lp) = c"
        using index_post old_index False by simp
      show ?thesis
        using cursor_some False final_index c_not_end
        by (simp add: raw_cursor_at_def list_remove_abs_def)
    qed
  qed
qed

definition raw_remove_effect ::
  "heap_mem \<Rightarrow> heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow> raw_node_id \<Rightarrow> bool"
where
  "raw_remove_effect h h' lp xs p \<longleftrightarrow>
     uxNumberOfItems_C (h_val h' lp) =
       uxNumberOfItems_C (h_val h lp) - 1 \<and>
     pxIndex_C (h_val h' lp) =
       (if pxIndex_C (h_val h lp) = p
        then raw_prev_at h lp p
        else pxIndex_C (h_val h lp)) \<and>
     raw_ring_links h' lp (remove1 p (ring xs)) \<and>
     (\<forall>q \<in> set (remove1 p (ring xs)).
        raw_key_at h' q = raw_key_at h q \<and>
        pvContainer_C (h_val h' q) = pvContainer_C (h_val h q))"

theorem raw_remove_effect_refines:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
    and effect: "raw_remove_effect h h' lp xs p"
  shows "raw_xlist_rel h' lp (list_remove_abs p xs)"
proof -
  have count_word:
    "uxNumberOfItems_C (h_val h' lp) =
     uxNumberOfItems_C (h_val h lp) - 1"
    using effect by (simp add: raw_remove_effect_def)
  have count_nat:
    "unat (uxNumberOfItems_C (h_val h' lp)) =
     length (remove1 p (ring xs))"
    using count_word raw_xlist_remove_count_transfer[OF rel member]
    by simp
  have index_post:
    "pxIndex_C (h_val h' lp) =
     (if pxIndex_C (h_val h lp) = p
      then raw_prev_at h lp p
      else pxIndex_C (h_val h lp))"
    using effect by (simp add: raw_remove_effect_def)
  have cursor_post:
    "raw_cursor_at h' lp = cursor (list_remove_abs p xs)"
    by (rule raw_xlist_remove_cursor_transfer[OF rel member index_post])
  have links:
    "raw_ring_links h' lp (remove1 p (ring xs))"
    using effect by (simp add: raw_remove_effect_def)
  have live:
    "\<And>q. q \<in> set (remove1 p (ring xs)) \<Longrightarrow>
      raw_key_at h' q = raw_key_at h q \<and>
      pvContainer_C (h_val h' q) = pvContainer_C (h_val h q)"
    using effect by (auto simp: raw_remove_effect_def)
  show ?thesis
    by (rule raw_xlist_rel_removeI[
          OF rel member count_nat cursor_post links live])
qed

end
