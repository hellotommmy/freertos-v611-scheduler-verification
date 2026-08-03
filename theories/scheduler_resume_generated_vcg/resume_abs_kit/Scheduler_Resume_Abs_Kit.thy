theory Scheduler_Resume_Abs_Kit
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Insert_Key_Frame.Scheduler_Resume_Generated_Insert_Key_Frame"
begin

text \<open>
  Pure list facts missing from the model kit: how the tail cursor, the last
  element, and the predecessor behave under end insertion and member
  removal.  They are needed to prove that the abstract one-task resume
  preserves the core well-formedness invariant, which the drained gate
  relation must carry.
\<close>

section \<open>End insertion appends\<close>

lemma insert_after_last_append:
  assumes distinct: "distinct xs"
    and nonempty: "xs \<noteq> []"
  shows "insert_after (last xs) x xs = xs @ [x]"
  using distinct nonempty
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases "ys = []")
    case True
    then show ?thesis by simp
  next
    case False
    have last_tail: "last (y # ys) = last ys"
      using False by simp
    have y_not_last: "y \<noteq> last ys"
      using Cons.prems False last_in_set by auto
    have tail: "insert_after (last ys) x ys = ys @ [x]"
      using Cons False by simp
    show ?thesis
      using last_tail y_not_last tail by simp
  qed
qed

section \<open>Last element under member removal\<close>

lemma last_remove1_not_last:
  assumes distinct: "distinct xs"
    and member: "x \<in> set xs"
    and not_last: "x \<noteq> last xs"
  shows "last (remove1 x xs) = last xs"
  using distinct member not_last
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases "y = x")
    case True
    have ys_nonempty: "ys \<noteq> []"
      using Cons.prems True by auto
    show ?thesis
      using True ys_nonempty by simp
  next
    case False
    have member_tail: "x \<in> set ys"
      using Cons.prems False by simp
    have ys_nonempty: "ys \<noteq> []"
      using member_tail by auto
    have removed_nonempty: "remove1 x ys \<noteq> []"
    proof
      assume empty: "remove1 x ys = []"
      obtain "as" bs where split: "ys = as @ x # bs"
          and fresh_as: "x \<notin> set as"
        using split_list_first[OF member_tail] by blast
      have removed: "remove1 x ys = as @ bs"
        using split fresh_as by (simp add: remove1_append)
      have single: "ys = [x]"
        using empty removed split by simp
      show False
        using Cons.prems(3) False single by simp
    qed
    have not_last_tail: "x \<noteq> last ys"
      using Cons.prems ys_nonempty by simp
    have tail: "last (remove1 x ys) = last ys"
      using Cons.IH Cons.prems(1) member_tail not_last_tail by simp
    show ?thesis
      using False ys_nonempty removed_nonempty tail by simp
  qed
qed

lemma remove1_last_butlast:
  assumes distinct: "distinct xs"
    and nonempty: "xs \<noteq> []"
  shows "remove1 (last xs) xs = butlast xs"
  using distinct nonempty
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases "ys = []")
    case True
    then show ?thesis by simp
  next
    case False
    have y_not_last: "y \<noteq> last ys"
      using Cons.prems False last_in_set by auto
    have tail: "remove1 (last ys) ys = butlast ys"
      using Cons False by simp
    show ?thesis
      using False y_not_last tail by simp
  qed
qed

section \<open>Predecessor of the last element\<close>

lemma predecessor_aux_last:
  assumes distinct: "distinct xs"
    and nonempty: "xs \<noteq> []"
    and fresh: "last xs \<notin> set (butlast xs)"
    and outside: "previous \<notin> set xs"
  shows
    "predecessor_aux previous (last xs) xs =
       Some (if butlast xs = [] then previous else last (butlast xs))"
  using distinct nonempty fresh outside
proof (induction xs arbitrary: previous)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases "ys = []")
    case True
    then show ?thesis by simp
  next
    case False
    have y_not_last: "y \<noteq> last (y # ys)"
      using Cons.prems False last_in_set by auto
    have tail_distinct: "distinct ys"
      using Cons.prems(1) by simp
    have y_out: "y \<notin> set ys"
      using Cons.prems(1) by simp
    have tail_fresh: "last ys \<notin> set (butlast ys)"
      using Cons.prems(3) False by simp
    have tail:
      "predecessor_aux y (last ys) ys =
         Some (if butlast ys = [] then y else last (butlast ys))"
      using Cons.IH[OF tail_distinct False tail_fresh y_out] .
    show ?thesis
      using False y_not_last tail by simp
  qed
qed

lemma predecessor_last:
  assumes distinct: "distinct xs"
    and long: "2 \<le> length xs"
  shows "predecessor (last xs) xs = Some (last (butlast xs))"
proof (cases xs)
  case Nil
  then show ?thesis using long by simp
next
  case (Cons y ys)
  have ys_nonempty: "ys \<noteq> []"
    using Cons long by (cases ys) auto
  have y_not_last: "y \<noteq> last (y # ys)"
    using Cons distinct ys_nonempty last_in_set by auto
  have tail_distinct: "distinct ys"
    using Cons distinct by simp
  have tail_fresh: "last ys \<notin> set (butlast ys)"
  proof
    assume inside: "last ys \<in> set (butlast ys)"
    have "distinct (butlast ys @ [last ys])"
      using tail_distinct ys_nonempty
      by (simp add: append_butlast_last_id)
    then show False using inside by simp
  qed
  have y_outside: "y \<notin> set ys"
    using Cons distinct by simp
  have aux:
    "predecessor_aux y (last ys) ys =
       Some (if butlast ys = [] then y else last (butlast ys))"
    by (rule predecessor_aux_last[
      OF tail_distinct ys_nonempty tail_fresh y_outside])
  show ?thesis
    using Cons ys_nonempty y_not_last aux
    by (cases "butlast ys = []") auto
qed

end
