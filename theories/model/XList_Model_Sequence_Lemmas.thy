theory XList_Model_Sequence_Lemmas
  imports XList_Model_Definitions
begin

lemma set_insert_after:
  assumes "c \<in> set xs"
  shows "set (insert_after c x xs) = insert x (set xs)"
  using assms by (induction xs) auto

lemma distinct_insert_after:
  assumes "distinct xs" "x \<notin> set xs" "c \<in> set xs"
  shows "distinct (insert_after c x xs)"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases "a = c")
    case True
    have c_ne_x: "c \<noteq> x"
      using Cons.prems(2) True by auto
    with True Cons.prems show ?thesis by simp
  next
    case False
    have tail_distinct: "distinct xs"
      using Cons.prems(1) by simp
    have x_fresh_tail: "x \<notin> set xs"
      using Cons.prems(2) by simp
    have c_in_tail: "c \<in> set xs"
      using Cons.prems(3) False by simp
    have inserted_tail_distinct: "distinct (insert_after c x xs)"
      using Cons.IH[OF tail_distinct x_fresh_tail c_in_tail] .
    have x_ne_a: "x \<noteq> a"
      using Cons.prems(2) by simp
    have a_ne_x: "a \<noteq> x"
      using x_ne_a by auto
    have a_notin_tail: "a \<notin> set xs"
      using Cons.prems(1) by simp
    have a_notin_inserted_tail: "a \<notin> set (insert_after c x xs)"
      using set_insert_after[OF c_in_tail] a_ne_x a_notin_tail by auto
    with False inserted_tail_distinct show ?thesis by simp
  qed
qed

lemma set_stable_key_insert[simp]:
  "set (stable_key_insert key x xs) = insert x (set xs)"
  by (induction xs) auto

lemma distinct_stable_key_insert:
  assumes "distinct xs" "x \<notin> set xs"
  shows "distinct (stable_key_insert key x xs)"
  using assms by (induction xs) auto

lemma sorted_stable_key_insert:
  assumes "sorted (map key xs)"
  shows "sorted (map key (stable_key_insert key x xs))"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  have tail_sorted: "sorted (map key ys)"
    using Cons.prems by simp
  have y_le_tail: "\<forall>z \<in> set ys. key y \<le> key z"
    using Cons.prems by simp
  have ih: "sorted (map key (stable_key_insert key x ys))"
    using Cons.IH[OF tail_sorted] .
  show ?case
  proof (cases "key x < key y")
    case True
    have x_le_y: "key x \<le> key y"
      using True by simp
    have x_le_tail: "\<forall>z \<in> set ys. key x \<le> key z"
    proof (intro ballI)
      fix z
      assume z_in: "z \<in> set ys"
      have "key y \<le> key z"
        using y_le_tail z_in by blast
      with x_le_y show "key x \<le> key z"
        by (rule order_trans)
    qed
    have x_le_all: "\<forall>z \<in> set (y # ys). key x \<le> key z"
      using x_le_y x_le_tail by simp
    show ?thesis
      using True Cons.prems x_le_all by simp
  next
    case False
    have y_le_x: "key y \<le> key x"
      using False by simp
    have y_le_inserted:
      "\<forall>z \<in> set (stable_key_insert key x ys). key y \<le> key z"
    proof (intro ballI)
      fix z
      assume z_in: "z \<in> set (stable_key_insert key x ys)"
      have "z = x \<or> z \<in> set ys"
        using z_in by simp
      then show "key y \<le> key z"
      proof
        assume "z = x"
        with y_le_x show ?thesis by simp
      next
        assume "z \<in> set ys"
        with y_le_tail show ?thesis by blast
      qed
    qed
    show ?thesis
      using False ih y_le_inserted by simp
  qed
qed

end
