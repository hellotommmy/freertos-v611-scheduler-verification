theory Scheduler_Event_Root_Family_Remove_Decoder_Remove1
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Rel.Scheduler_Event_Root_Family_Rel"
begin

text \<open>
  Exact preservation of the arbitrary finite Event-root family by one real
  remove transformer.  No task, root, ring position, cursor, key, address, or
  ring length is fixed.  The physical owner and abstract owner are updated by
  their respective list_remove_abs operations; every other root is framed.

  The first lemmas establish the missing structural fact: a functional
  decoder relabelling commutes with removal, including the cursor/predecessor
  case.  Distinctness on both rings is essential.  Without it two concrete
  nodes could decode to the same abstract node, and remove1 could delete
  different occurrences.
\<close>

lemma list_all2_decoder_remove1:
  assumes pairs:
      "list_all2 (\<lambda>q m. D q = Some m) qs ms"
    and q_distinct: "distinct qs"
    and m_distinct: "distinct ms"
    and member: "p \<in> set qs"
    and decode: "D p = Some n"
  shows
    "list_all2 (\<lambda>q m. D q = Some m)
       (remove1 p qs) (remove1 n ms)"
  using pairs q_distinct m_distinct member decode
proof (induction qs arbitrary: ms p n)
  case Nil
  then show ?case by simp
next
  case (Cons q qs)
  obtain m ms' where ms: "ms = m # ms'"
    using Cons.prems(1) by (cases ms) auto
  have head: "D q = Some m"
    and tail: "list_all2 (\<lambda>q m. D q = Some m) qs ms'"
    using Cons.prems(1) by (simp_all add: ms)
  have q_tail_distinct: "distinct qs"
    and m_tail_distinct: "distinct ms'"
    using Cons.prems(2,3) by (simp_all add: ms)
  show ?case
  proof (cases "q = p")
    case True
    have mn: "m = n"
      using head Cons.prems(5) True by simp
    show ?thesis
      using tail True mn by (simp add: ms)
  next
    case False
    have p_tail: "p \<in> set qs"
      using Cons.prems(4) False by simp
    obtain n' where n'_tail: "n' \<in> set ms'"
      and decode': "D p = Some n'"
      using list_all2_decoder_left_closed[OF tail p_tail] by blast
    have n'_eq: "n' = n"
      using Cons.prems(5) decode' by simp
    have n_tail: "n \<in> set ms'"
      using n'_tail n'_eq by simp
    have m_ne: "m \<noteq> n"
      using Cons.prems(3) n_tail by (auto simp: ms)
    have ih:
      "list_all2 (\<lambda>q m. D q = Some m)
         (remove1 p qs) (remove1 n ms')"
      by (rule Cons.IH[OF tail q_tail_distinct m_tail_distinct
            p_tail Cons.prems(5)])
    show ?thesis
      using head ih False m_ne by (simp add: ms)
  qed
qed

end
