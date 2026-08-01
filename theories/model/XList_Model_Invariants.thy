theory XList_Model_Invariants
  imports XList_Model_Predecessor_Lemmas
begin

theorem list_insert_end_preserves_wf:
  assumes "xlist_wf xs" "x \<notin> set (ring xs)"
  shows "xlist_wf (list_insert_end_abs x k xs)"
proof (cases "cursor xs")
  case None
  with assms show ?thesis
    unfolding xlist_wf_def list_insert_end_abs_def by simp
next
  case (Some c)
  have ring_distinct: "distinct (ring xs)"
    using assms(1) unfolding xlist_wf_def by simp
  have c_in_ring: "c \<in> set (ring xs)"
    using assms(1) Some unfolding xlist_wf_def by simp
  have inserted_distinct: "distinct (insert_after c x (ring xs))"
    using distinct_insert_after[OF ring_distinct assms(2) c_in_ring] .
  have x_in_inserted: "x \<in> set (insert_after c x (ring xs))"
    using set_insert_after[OF c_in_ring] by simp
  show ?thesis
    using Some inserted_distinct x_in_inserted
    unfolding xlist_wf_def list_insert_end_abs_def by simp
qed

theorem list_insert_ordered_preserves_wf:
  assumes "xlist_wf xs" "x \<notin> set (ring xs)"
  shows "xlist_wf (list_insert_ordered_abs x k xs)"
  using assms distinct_stable_key_insert
  unfolding xlist_wf_def list_insert_ordered_abs_def Let_def
  by (cases "cursor xs") auto

theorem list_insert_ordered_is_sorted:
  assumes "sorted (map ((item_key xs)(x := k)) (ring xs))"
  shows "sorted
    (map (item_key (list_insert_ordered_abs x k xs))
      (ring (list_insert_ordered_abs x k xs)))"
  using assms sorted_stable_key_insert
  unfolding list_insert_ordered_abs_def Let_def by simp

theorem list_remove_preserves_wf:
  assumes "xlist_wf xs" "x \<in> set (ring xs)"
  shows "xlist_wf (list_remove_abs x xs)"
proof (cases "cursor xs")
  case None
  with assms show ?thesis
    unfolding xlist_wf_def list_remove_abs_def
    by (simp add: distinct_remove1)
next
  case (Some c)
  have cursor_eq: "cursor xs = Some c"
    using Some .
  have ring_distinct: "distinct (ring xs)"
    using assms(1) unfolding xlist_wf_def by simp
  have c_in_ring: "c \<in> set (ring xs)"
    using assms(1) cursor_eq unfolding xlist_wf_def by simp
  show ?thesis
  proof (cases "c = x")
    case False
    have c_survives: "c \<in> set (remove1 x (ring xs))"
      using c_in_ring False by simp
    show ?thesis
      using cursor_eq False ring_distinct c_survives
      unfolding xlist_wf_def list_remove_abs_def
      by (simp add: distinct_remove1)
  next
    case True
    show ?thesis
    proof (cases "predecessor x (ring xs)")
      case None
      show ?thesis
        using cursor_eq True None ring_distinct
        unfolding xlist_wf_def list_remove_abs_def
        by (simp add: distinct_remove1)
    next
      case (Some p)
      have p_survives: "p \<in> set (remove1 x (ring xs))"
        using predecessor_not_removed[OF ring_distinct Some] .
      show ?thesis
        using cursor_eq True Some ring_distinct p_survives
        unfolding xlist_wf_def list_remove_abs_def
        by (simp add: distinct_remove1)
    qed
  qed
qed

end
