theory XList_Model_Predecessor_Lemmas
  imports XList_Model_Sequence_Lemmas
begin

lemma predecessor_aux_member:
  assumes "predecessor_aux previous x xs = Some p"
  shows "p = previous \<or> p \<in> set xs"
  using assms
proof (induction xs arbitrary: previous)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases "y = x")
    case True
    with Cons.prems show ?thesis by simp
  next
    case False
    have step: "predecessor_aux y x ys = Some p"
      using Cons.prems False by simp
    have "p = y \<or> p \<in> set ys"
      using Cons.IH[OF step] .
    then show ?thesis by auto
  qed
qed

lemma predecessor_member:
  assumes "predecessor x xs = Some p"
  shows "p \<in> set xs"
proof (cases xs)
  case Nil
  with assms show ?thesis by simp
next
  case (Cons y ys)
  show ?thesis
  proof (cases "y = x")
    case True
    with Cons assms show ?thesis by simp
  next
    case False
    have step: "predecessor_aux y x ys = Some p"
      using Cons False assms by simp
    have "p = y \<or> p \<in> set ys"
      using predecessor_aux_member[OF step] .
    with Cons show ?thesis by auto
  qed
qed

lemma predecessor_aux_survives_remove1:
  assumes "distinct (previous # xs)"
    and "predecessor_aux previous x xs = Some p"
  shows "p \<in> set (remove1 x (previous # xs))"
  using assms
proof (induction xs arbitrary: previous)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases "y = x")
    case True
    with Cons.prems show ?thesis by simp
  next
    case False
    have tail_distinct: "distinct (y # ys)"
      using Cons.prems(1) by simp
    have step: "predecessor_aux y x ys = Some p"
      using Cons.prems(2) False by simp
    have ih: "p \<in> set (remove1 x (y # ys))"
      using Cons.IH[OF tail_distinct step] .
    show ?thesis
    proof (cases "previous = x")
      case True
      have removed_subset:
        "set (remove1 x (y # ys)) \<subseteq> set (y # ys)"
        by (rule set_remove1_subset)
      have p_in_tail: "p \<in> set (y # ys)"
        using removed_subset ih by (rule subsetD)
      with True show ?thesis by simp
    next
      case False
      with ih show ?thesis by simp
    qed
  qed
qed

lemma predecessor_not_removed:
  assumes "distinct xs" "predecessor x xs = Some p"
  shows "p \<in> set (remove1 x xs)"
proof (cases xs)
  case Nil
  with assms show ?thesis by simp
next
  case (Cons y ys)
  show ?thesis
  proof (cases "y = x")
    case True
    with Cons assms show ?thesis by simp
  next
    case False
    have tail_distinct: "distinct (y # ys)"
      using Cons assms(1) by simp
    have step: "predecessor_aux y x ys = Some p"
      using Cons False assms(2) by simp
    have "p \<in> set (remove1 x (y # ys))"
      using predecessor_aux_survives_remove1[OF tail_distinct step] .
    with Cons show ?thesis by simp
  qed
qed

end
