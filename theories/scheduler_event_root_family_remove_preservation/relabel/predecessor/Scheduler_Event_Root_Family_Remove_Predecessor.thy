theory Scheduler_Event_Root_Family_Remove_Predecessor
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Decoder_Remove1.Scheduler_Event_Root_Family_Remove_Decoder_Remove1"
begin

lemma list_all2_decoder_predecessor_aux:
  assumes pairs:
      "list_all2 (\<lambda>q m. D q = Some m) qs ms"
    and previous: "D previous_q = Some previous_m"
    and q_distinct: "distinct (previous_q # qs)"
    and m_distinct: "distinct (previous_m # ms)"
    and member: "p \<in> set qs"
    and decode: "D p = Some n"
  shows
    "rel_option (\<lambda>q m. D q = Some m)
       (predecessor_aux previous_q p qs)
       (predecessor_aux previous_m n ms)"
  using pairs previous q_distinct m_distinct member decode
proof (induction qs arbitrary: ms previous_q previous_m p n)
  case Nil
  then show ?case by simp
next
  case (Cons q qs)
  obtain m ms' where ms: "ms = m # ms'"
    using Cons.prems(1) by (cases ms) auto
  have head: "D q = Some m"
    and tail: "list_all2 (\<lambda>q m. D q = Some m) qs ms'"
    using Cons.prems(1) by (simp_all add: ms)
  show ?case
  proof (cases "q = p")
    case True
    have mn: "m = n"
      using head Cons.prems(6) True by simp
    show ?thesis
      using Cons.prems(2) True mn by (simp add: ms)
  next
    case False
    have p_tail: "p \<in> set qs"
      using Cons.prems(5) False by simp
    obtain n' where n'_tail: "n' \<in> set ms'"
      and decode': "D p = Some n'"
      using list_all2_decoder_left_closed[OF tail p_tail] by blast
    have n'_eq: "n' = n"
      using Cons.prems(6) decode' by simp
    have n_tail: "n \<in> set ms'"
      using n'_tail n'_eq by simp
    have m_ne: "m \<noteq> n"
      using Cons.prems(4) n_tail by (auto simp: ms)
    have q_tail_distinct: "distinct (q # qs)"
      and m_tail_distinct: "distinct (m # ms')"
      using Cons.prems(3,4) by (simp_all add: ms)
    have ih:
      "rel_option (\<lambda>q m. D q = Some m)
         (predecessor_aux q p qs)
         (predecessor_aux m n ms')"
      by (rule Cons.IH[OF tail head q_tail_distinct m_tail_distinct
            p_tail Cons.prems(6)])
    show ?thesis
      using ih False m_ne by (simp add: ms)
  qed
qed

lemma list_all2_decoder_predecessor:
  assumes pairs:
      "list_all2 (\<lambda>q m. D q = Some m) qs ms"
    and q_distinct: "distinct qs"
    and m_distinct: "distinct ms"
    and member: "p \<in> set qs"
    and decode: "D p = Some n"
  shows
    "rel_option (\<lambda>q m. D q = Some m)
       (predecessor p qs) (predecessor n ms)"
proof (cases qs)
  case Nil
  then show ?thesis using member by simp
next
  case (Cons q qs')
  obtain m ms' where ms: "ms = m # ms'"
    using pairs Cons by (cases ms) auto
  have head: "D q = Some m"
    and tail: "list_all2 (\<lambda>q m. D q = Some m) qs' ms'"
    using pairs by (simp_all add: Cons ms)
  show ?thesis
  proof (cases "q = p")
    case True
    have mn: "m = n"
      using head decode True by simp
    show ?thesis using True mn by (simp add: Cons ms)
  next
    case False
    have p_tail: "p \<in> set qs'"
      using member False by (simp add: Cons)
    obtain n' where n'_tail: "n' \<in> set ms'"
      and decode': "D p = Some n'"
      using list_all2_decoder_left_closed[OF tail p_tail] by blast
    have n'_eq: "n' = n"
      using decode decode' by simp
    have n_tail: "n \<in> set ms'"
      using n'_tail n'_eq by simp
    have m_ne: "m \<noteq> n"
      using m_distinct n_tail by (auto simp: ms)
    have aux:
      "rel_option (\<lambda>q m. D q = Some m)
         (predecessor_aux q p qs')
         (predecessor_aux m n ms')"
      by (rule list_all2_decoder_predecessor_aux[
            OF tail head _ _ p_tail decode])
         (use q_distinct m_distinct in \<open>simp_all add: Cons ms\<close>)
    show ?thesis
      using aux False m_ne by (simp add: Cons ms)
  qed
qed

end
