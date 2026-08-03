theory Scheduler_List_All2_Insert_After
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Preservation.Scheduler_Family_Insert_End_Preservation"
begin

lemma list_all2_decoder_insert_after:
  assumes pairs:
      "list_all2 (\<lambda>q m. D q = Some m) qs ms"
    and abs_distinct: "distinct ms"
    and member: "c \<in> set qs"
    and cursor_decode: "D c = Some d"
    and inserted_decode: "D p = Some n"
  shows
    "list_all2 (\<lambda>q m. D q = Some m)
       (insert_after c p qs) (insert_after d n ms)"
  using pairs abs_distinct member cursor_decode inserted_decode
proof (induction qs arbitrary: ms)
  case Nil
  then show ?case by simp
next
  case (Cons q qs)
  obtain m ms' where ms: "ms = m # ms'"
    using Cons.prems(1) by (cases ms) auto
  have head: "D q = Some m"
    and tail: "list_all2 (\<lambda>q m. D q = Some m) qs ms'"
    using Cons.prems(1) by (simp_all add: ms)
  have tail_distinct: "distinct ms'"
    using Cons.prems(2) by (simp add: ms)
  show ?case
  proof (cases "q = c")
    case True
    have md: "m = d"
      using head Cons.prems(4) True by simp
    show ?thesis
      using head tail Cons.prems(5) True md by (simp add: ms)
  next
    case False
    have c_tail: "c \<in> set qs"
      using Cons.prems(3) False by simp
    obtain d' where d'_tail: "d' \<in> set ms'"
      and decode': "D c = Some d'"
      using list_all2_decoder_left_closed[OF tail c_tail] by blast
    have d'_eq: "d' = d"
      using Cons.prems(4) decode' by simp
    have d_tail: "d \<in> set ms'"
      using d'_tail d'_eq by simp
    have m_ne: "m \<noteq> d"
      using Cons.prems(2) d_tail by (auto simp: ms)
    have ih:
      "list_all2 (\<lambda>q m. D q = Some m)
         (insert_after c p qs) (insert_after d n ms')"
      by (rule Cons.IH[OF tail tail_distinct c_tail
            Cons.prems(4) Cons.prems(5)])
    show ?thesis
      using head ih False m_ne by (simp add: ms)
  qed
qed

end
