theory List_V611_Raw_R6_Unlink_Projection
  imports "EAL6_FreeRTOS_V611_List_Raw_R6_Insert_Relation.List_V611_Raw_R6_Insert_Relation"
begin

text \<open>
  Alias-safe field projection for the two unlink writes.  The observation
  bridge is valid for both real items and the embedded sentinel; no assumption
  separates predecessor from successor, so singleton rings remain covered.
\<close>

lemma raw_next_field_update_to_whole:
  assumes guard: "c_guard u"
  shows
    "heap_update (raw_next_field_ptr u) q h =
     heap_update u
       (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. q) (h_val h u)) h"
  unfolding raw_next_field_ptr_def
  by (rule xLIST_ITEM_C_heap_update_fields(2)[OF guard])

lemma raw_previous_field_update_to_whole:
  assumes guard: "c_guard u"
  shows
    "heap_update (raw_previous_field_ptr u) q h =
     heap_update u
       (xLIST_ITEM_C.pxPrevious_C_update (\<lambda>_. q) (h_val h u)) h"
  unfolding raw_previous_field_ptr_def
  by (rule xLIST_ITEM_C_heap_update_fields(3)[OF guard])

lemma raw_next_at_after_same_node_next_field_update:
  assumes guard: "c_guard u"
  shows
    "raw_next_at (heap_update (raw_next_field_ptr u) q h) lp u = q"
proof -
  let ?h' = "heap_update (raw_next_field_ptr u) q h"
  have readback:
    "xLIST_ITEM_C.pxNext_C (h_val ?h' u) = q"
    using raw_next_field_update_to_whole[OF guard, where q=q and h=h]
      guard
    by (simp add: h_val_heap_update)
  have bridge:
    "xLIST_ITEM_C.pxNext_C (h_val ?h' u) = raw_next_at ?h' lp u"
    by (rule raw_full_next_is_sentinel_safe)
  show ?thesis using readback bridge by simp
qed

lemma raw_prev_at_after_same_node_previous_field_update:
  assumes guard: "c_guard u"
  shows
    "raw_prev_at (heap_update (raw_previous_field_ptr u) q h) lp u = q"
proof -
  let ?h' = "heap_update (raw_previous_field_ptr u) q h"
  have readback:
    "xLIST_ITEM_C.pxPrevious_C (h_val ?h' u) = q"
    using raw_previous_field_update_to_whole[OF guard, where q=q and h=h]
      guard
    by (simp add: h_val_heap_update)
  have bridge:
    "xLIST_ITEM_C.pxPrevious_C (h_val ?h' u) = raw_prev_at ?h' lp u"
    by (rule raw_full_previous_is_sentinel_safe)
  show ?thesis using readback bridge by simp
qed

lemma raw_prev_at_survives_same_node_next_field_update:
  assumes guard: "c_guard u"
  shows
    "raw_prev_at (heap_update (raw_next_field_ptr u) q h) lp u =
     raw_prev_at h lp u"
proof -
  let ?h' = "heap_update (raw_next_field_ptr u) q h"
  have unchanged:
    "xLIST_ITEM_C.pxPrevious_C (h_val ?h' u) =
     xLIST_ITEM_C.pxPrevious_C (h_val h u)"
    using raw_next_field_update_to_whole[OF guard, where q=q and h=h]
      guard
    by (simp add: h_val_heap_update)
  have after_bridge:
    "xLIST_ITEM_C.pxPrevious_C (h_val ?h' u) = raw_prev_at ?h' lp u"
    by (rule raw_full_previous_is_sentinel_safe)
  have before_bridge:
    "xLIST_ITEM_C.pxPrevious_C (h_val h u) = raw_prev_at h lp u"
    by (rule raw_full_previous_is_sentinel_safe)
  show ?thesis using unchanged after_bridge before_bridge by simp
qed

lemma raw_next_at_survives_same_node_previous_field_update:
  assumes guard: "c_guard u"
  shows
    "raw_next_at (heap_update (raw_previous_field_ptr u) q h) lp u =
     raw_next_at h lp u"
proof -
  let ?h' = "heap_update (raw_previous_field_ptr u) q h"
  have unchanged:
    "xLIST_ITEM_C.pxNext_C (h_val ?h' u) =
     xLIST_ITEM_C.pxNext_C (h_val h u)"
    using raw_previous_field_update_to_whole[OF guard, where q=q and h=h]
      guard
    by (simp add: h_val_heap_update)
  have after_bridge:
    "xLIST_ITEM_C.pxNext_C (h_val ?h' u) = raw_next_at ?h' lp u"
    by (rule raw_full_next_is_sentinel_safe)
  have before_bridge:
    "xLIST_ITEM_C.pxNext_C (h_val h u) = raw_next_at h lp u"
    by (rule raw_full_next_is_sentinel_safe)
  show ?thesis using unchanged after_bridge before_bridge by simp
qed

lemma raw_pointer_field_update_preserves_disjoint_list:
  assumes disjoint:
    "raw_pointer_field_region f \<inter> raw_list_region lp = {}"
  shows
    "h_val (heap_update f (q :: raw_node_id) h) lp = h_val h lp"
proof -
  have byte_disjoint:
    "{ptr_val f..+
       length (to_bytes q
         (heap_list h (size_of TYPE(raw_node_id)) (ptr_val f)))} \<inter>
     {ptr_val lp..+size_of TYPE(xLIST_C)} = {}"
    using disjoint
    by (simp add: raw_pointer_field_region_def raw_list_region_def)
  have heap_lists_same:
    "heap_list
       (heap_update_list (ptr_val f)
         (to_bytes q
           (heap_list h (size_of TYPE(raw_node_id)) (ptr_val f))) h)
       (size_of TYPE(xLIST_C)) (ptr_val lp) =
     heap_list h (size_of TYPE(xLIST_C)) (ptr_val lp)"
    by (rule heap_list_update_disjoint_same[OF byte_disjoint])
  show ?thesis
    unfolding h_val_def heap_update_def
    using heap_lists_same by simp
qed

lemma raw_cycle_observations_survive_other_next_field_update:
  assumes layout: "raw_xlist_layout lp rs"
    and write_member:
      "u \<in> insert (raw_end_item lp) (set rs)"
    and observe_member:
      "v \<in> insert (raw_end_item lp) (set rs)"
    and different: "u \<noteq> v"
  shows
    "raw_next_at (heap_update (raw_next_field_ptr u) q h) lp v =
       raw_next_at h lp v \<and>
     raw_prev_at (heap_update (raw_next_field_ptr u) q h) lp v =
       raw_prev_at h lp v"
proof (cases "v = raw_end_item lp")
  case True
  have u_not_end: "u \<noteq> raw_end_item lp"
    using different True by auto
  have u_real: "u \<in> set rs"
    using write_member u_not_end by simp
  have item_list_disjoint:
    "raw_item_region u \<inter> raw_list_region lp = {}"
    using layout u_real by (auto simp: raw_xlist_layout_def)
  have field_list_disjoint:
    "raw_pointer_field_region (raw_next_field_ptr u) \<inter>
     raw_list_region lp = {}"
    using raw_next_field_region_subset_item[where u=u]
      item_list_disjoint by blast
  have list_same:
    "h_val (heap_update (raw_next_field_ptr u) q h) lp = h_val h lp"
    by (rule raw_pointer_field_update_preserves_disjoint_list[
          OF field_list_disjoint])
  show ?thesis using True list_same by simp
next
  case False
  have v_real: "v \<in> set rs"
    using observe_member False by simp
  have field_item_disjoint:
    "raw_pointer_field_region (raw_next_field_ptr u) \<inter>
     raw_item_region v = {}"
    by (rule raw_cycle_next_field_disjoint_from_other_item[
          OF layout v_real write_member different])
  have item_same:
    "h_val (heap_update (raw_next_field_ptr u) q h) v = h_val h v"
    by (rule raw_pointer_field_update_preserves_disjoint_item[
          OF field_item_disjoint])
  show ?thesis using False item_same
    by (simp add: raw_next_at_def raw_prev_at_def)
qed

lemma raw_cycle_observations_survive_other_previous_field_update:
  assumes layout: "raw_xlist_layout lp rs"
    and write_member:
      "u \<in> insert (raw_end_item lp) (set rs)"
    and observe_member:
      "v \<in> insert (raw_end_item lp) (set rs)"
    and different: "u \<noteq> v"
  shows
    "raw_next_at (heap_update (raw_previous_field_ptr u) q h) lp v =
       raw_next_at h lp v \<and>
     raw_prev_at (heap_update (raw_previous_field_ptr u) q h) lp v =
       raw_prev_at h lp v"
proof (cases "v = raw_end_item lp")
  case True
  have u_not_end: "u \<noteq> raw_end_item lp"
    using different True by auto
  have u_real: "u \<in> set rs"
    using write_member u_not_end by simp
  have item_list_disjoint:
    "raw_item_region u \<inter> raw_list_region lp = {}"
    using layout u_real by (auto simp: raw_xlist_layout_def)
  have field_list_disjoint:
    "raw_pointer_field_region (raw_previous_field_ptr u) \<inter>
     raw_list_region lp = {}"
    using raw_previous_field_region_subset_item[where u=u]
      item_list_disjoint by blast
  have list_same:
    "h_val (heap_update (raw_previous_field_ptr u) q h) lp = h_val h lp"
    by (rule raw_pointer_field_update_preserves_disjoint_list[
          OF field_list_disjoint])
  show ?thesis using True list_same by simp
next
  case False
  have v_real: "v \<in> set rs"
    using observe_member False by simp
  have field_item_disjoint:
    "raw_pointer_field_region (raw_previous_field_ptr u) \<inter>
     raw_item_region v = {}"
    by (rule raw_cycle_previous_field_disjoint_from_other_item[
          OF layout v_real write_member different])
  have item_same:
    "h_val (heap_update (raw_previous_field_ptr u) q h) v = h_val h v"
    by (rule raw_pointer_field_update_preserves_disjoint_item[
          OF field_item_disjoint])
  show ?thesis using False item_same
    by (simp add: raw_next_at_def raw_prev_at_def)
qed

definition raw_unlink_first ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow> heap_mem"
where
  "raw_unlink_first h lp p =
     heap_update
       (raw_previous_field_ptr (raw_next_at h lp p))
       (raw_prev_at h lp p) h"

definition raw_unlink_two ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow> heap_mem"
where
  "raw_unlink_two h lp p =
     heap_update
       (raw_next_field_ptr (raw_prev_at h lp p))
       (raw_next_at h lp p)
       (raw_unlink_first h lp p)"

lemma raw_unlink_two_writes_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_next_at (raw_unlink_two h lp p) lp (raw_prev_at h lp p) =
       raw_next_at h lp p \<and>
     raw_prev_at (raw_unlink_two h lp p) lp (raw_next_at h lp p) =
       raw_prev_at h lp p \<and>
     (\<forall>u \<in> insert (raw_end_item lp) (set (ring xs)).
        u \<noteq> raw_prev_at h lp p \<longrightarrow>
        raw_next_at (raw_unlink_two h lp p) lp u =
          raw_next_at h lp u) \<and>
     (\<forall>v \<in> insert (raw_end_item lp) (set (ring xs)).
        v \<noteq> raw_next_at h lp p \<longrightarrow>
        raw_prev_at (raw_unlink_two h lp p) lp v =
          raw_prev_at h lp v)"
proof -
  let ?cycle = "insert (raw_end_item lp) (set (ring xs))"
  let ?a = "raw_prev_at h lp p"
  let ?b = "raw_next_at h lp p"
  let ?h1 = "raw_unlink_first h lp p"
  let ?h2 = "raw_unlink_two h lp p"
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have p_cycle: "p \<in> ?cycle" using member by simp
  have a_cycle: "?a \<in> ?cycle"
    by (rule raw_ring_links_prev_closed[OF links p_cycle])
  have b_cycle: "?b \<in> ?cycle"
    by (rule raw_ring_links_next_closed[OF links p_cycle])
  have a_guard: "c_guard ?a"
    by (rule raw_xlist_rel_cycle_node_guard[OF rel a_cycle])
  have b_guard: "c_guard ?b"
    by (rule raw_xlist_rel_cycle_node_guard[OF rel b_cycle])
  have first_previous: "raw_prev_at ?h1 lp ?b = ?a"
    unfolding raw_unlink_first_def
    by (rule raw_prev_at_after_same_node_previous_field_update[OF b_guard])
  have first_next_frame:
    "\<And>u. u \<in> ?cycle \<Longrightarrow>
      raw_next_at ?h1 lp u = raw_next_at h lp u"
  proof -
    fix u
    assume u_cycle: "u \<in> ?cycle"
    show "raw_next_at ?h1 lp u = raw_next_at h lp u"
    proof (cases "u = ?b")
      case True
      show ?thesis
        unfolding raw_unlink_first_def
        using True raw_next_at_survives_same_node_previous_field_update[
          OF b_guard, where q="?a" and h=h and lp=lp]
        by simp
    next
      case False
      have b_ne_u: "?b \<noteq> u" using False by auto
      have observations:
        "raw_next_at
           (heap_update (raw_previous_field_ptr ?b) ?a h) lp u =
           raw_next_at h lp u \<and>
         raw_prev_at
           (heap_update (raw_previous_field_ptr ?b) ?a h) lp u =
           raw_prev_at h lp u"
        by (rule raw_cycle_observations_survive_other_previous_field_update[
              OF layout b_cycle u_cycle b_ne_u])
      show ?thesis
        using observations by (simp add: raw_unlink_first_def)
    qed
  qed
  have first_previous_frame:
    "\<And>v. v \<in> ?cycle \<Longrightarrow> v \<noteq> ?b \<Longrightarrow>
      raw_prev_at ?h1 lp v = raw_prev_at h lp v"
  proof -
    fix v
    assume v_cycle: "v \<in> ?cycle" and v_ne: "v \<noteq> ?b"
    have b_ne_v: "?b \<noteq> v" using v_ne by auto
    have observations:
      "raw_next_at
         (heap_update (raw_previous_field_ptr ?b) ?a h) lp v =
         raw_next_at h lp v \<and>
       raw_prev_at
         (heap_update (raw_previous_field_ptr ?b) ?a h) lp v =
         raw_prev_at h lp v"
      by (rule raw_cycle_observations_survive_other_previous_field_update[
            OF layout b_cycle v_cycle b_ne_v])
    show "raw_prev_at ?h1 lp v = raw_prev_at h lp v"
      using observations by (simp add: raw_unlink_first_def)
  qed
  have second_next: "raw_next_at ?h2 lp ?a = ?b"
    unfolding raw_unlink_two_def
    by (rule raw_next_at_after_same_node_next_field_update[OF a_guard])
  have second_previous_frame:
    "\<And>v. v \<in> ?cycle \<Longrightarrow>
      raw_prev_at ?h2 lp v = raw_prev_at ?h1 lp v"
  proof -
    fix v
    assume v_cycle: "v \<in> ?cycle"
    show "raw_prev_at ?h2 lp v = raw_prev_at ?h1 lp v"
    proof (cases "v = ?a")
      case True
      show ?thesis
        unfolding raw_unlink_two_def
        using True raw_prev_at_survives_same_node_next_field_update[
          OF a_guard, where q="?b" and h="?h1" and lp=lp]
        by simp
    next
      case False
      have a_ne_v: "?a \<noteq> v" using False by auto
      have observations:
        "raw_next_at
           (heap_update (raw_next_field_ptr ?a) ?b ?h1) lp v =
           raw_next_at ?h1 lp v \<and>
         raw_prev_at
           (heap_update (raw_next_field_ptr ?a) ?b ?h1) lp v =
           raw_prev_at ?h1 lp v"
        by (rule raw_cycle_observations_survive_other_next_field_update[
              OF layout a_cycle v_cycle a_ne_v])
      show ?thesis
        using observations by (simp add: raw_unlink_two_def)
    qed
  qed
  have second_next_frame:
    "\<And>u. u \<in> ?cycle \<Longrightarrow> u \<noteq> ?a \<Longrightarrow>
      raw_next_at ?h2 lp u = raw_next_at ?h1 lp u"
  proof -
    fix u
    assume u_cycle: "u \<in> ?cycle" and u_ne: "u \<noteq> ?a"
    have a_ne_u: "?a \<noteq> u" using u_ne by auto
    have observations:
      "raw_next_at
         (heap_update (raw_next_field_ptr ?a) ?b ?h1) lp u =
         raw_next_at ?h1 lp u \<and>
       raw_prev_at
         (heap_update (raw_next_field_ptr ?a) ?b ?h1) lp u =
         raw_prev_at ?h1 lp u"
      by (rule raw_cycle_observations_survive_other_next_field_update[
            OF layout a_cycle u_cycle a_ne_u])
    show "raw_next_at ?h2 lp u = raw_next_at ?h1 lp u"
      using observations by (simp add: raw_unlink_two_def)
  qed
  have bridge_previous: "raw_prev_at ?h2 lp ?b = ?a"
    using second_previous_frame[OF b_cycle] first_previous by simp
  have final_next_frame:
    "\<And>u. u \<in> ?cycle \<Longrightarrow> u \<noteq> ?a \<Longrightarrow>
      raw_next_at ?h2 lp u = raw_next_at h lp u"
    using second_next_frame first_next_frame by simp
  have final_previous_frame:
    "\<And>v. v \<in> ?cycle \<Longrightarrow> v \<noteq> ?b \<Longrightarrow>
      raw_prev_at ?h2 lp v = raw_prev_at h lp v"
    using second_previous_frame first_previous_frame by simp
  show ?thesis
    using second_next bridge_previous final_next_frame final_previous_frame
    by blast
qed

corollary raw_unlink_two_writes_ring_links:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_ring_links (raw_unlink_two h lp p) lp
       (remove1 p (ring xs))"
proof -
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have distinct: "distinct (raw_end_item lp # ring xs)"
    by (rule raw_xlist_rel_distinct_cycle_nodes[OF rel])
  note effect = raw_unlink_two_writes_effect[OF rel member]
  show ?thesis
    apply (rule raw_ring_links_delete[OF links distinct member])
    using effect
    apply blast+
    done
qed

end
