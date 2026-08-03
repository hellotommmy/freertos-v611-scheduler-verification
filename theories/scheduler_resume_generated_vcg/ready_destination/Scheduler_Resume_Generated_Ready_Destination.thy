theory Scheduler_Resume_Generated_Ready_Destination
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Ready_Array_ABI.Scheduler_Resume_Generated_Ready_Array_ABI"
begin

text \<open>
  The generated pending-ready drain body selects its destination queue by
  \<open>array_ptr_index pxReadyTasksLists_' False (unat uxPriority)\<close>, immediately
  after its own \<open>guard (uxPriority < 4)\<close>.  This theory identifies that
  computed pointer with the indexed scheduler root \<open>sr_ready\<close>, and derives its
  guard and separation obligations for an arbitrary in-range priority rather
  than for a fixed one.  The bound is supplied by the source guard, so it is
  not an added scope restriction.
\<close>

lemma generated_ready_root_is_array_index:
  "array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_' False i =
     sr_ready generated_scheduler_roots i"
  by (simp add: generated_scheduler_roots_def)

lemma generated_ready_root_exact:
  "sr_ready generated_scheduler_roots 0 = Ptr 0x00102020"
  "sr_ready generated_scheduler_roots 1 = Ptr 0x00102034"
  "sr_ready generated_scheduler_roots 2 = Ptr 0x00102048"
  "sr_ready generated_scheduler_roots 3 = Ptr 0x0010205c"
  by (simp_all add: generated_scheduler_roots_def
      Scheduler_V611_Parse.pxReadyTasksLists_'_def
      array_ptr_index_def ptr_add_def
      Scheduler_V611_Parse.xLIST_C_size_of)

lemma generated_ready_root_member:
  assumes bound: "i < 4"
  shows
    "sr_ready generated_scheduler_roots i
       \<in> set (p2_physical_roots generated_scheduler_roots)"
proof -
  have cases: "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
    using bound by linarith
  from cases show ?thesis
    by (auto simp: p2_physical_roots_def)
qed

lemma generated_ready_root_guard:
  assumes bound: "i < 4"
  shows "c_guard (sr_ready generated_scheduler_roots i)"
  using frozen_p2_physical_roots_guarded generated_ready_root_member[OF bound]
  by blast

lemma generated_ready_root_disjoint:
  assumes bound: "i < 4"
    and other: "lq \<in> set (p2_physical_roots generated_scheduler_roots)"
    and distinct: "sr_ready generated_scheduler_roots i \<noteq> lq"
  shows
    "scheduler_list_region (sr_ready generated_scheduler_roots i)
       \<inter> scheduler_list_region lq = {}"
  using frozen_p2_physical_roots_pairwise_disjoint
    generated_ready_root_member[OF bound] other distinct
  by blast

text \<open>
  The source reads a 32-bit priority word, so the in-range hypothesis arrives
  in word order.  This is the bridge to the natural index above.
\<close>

lemma generated_ready_priority_word_bound:
  assumes bound: "(w :: 32 word) < 4"
  shows "unat w < 4"
  using bound by (simp add: word_less_nat_alt)

theorem generated_ready_destination_from_priority_word:
  assumes bound: "(w :: 32 word) < 4"
  shows
    "array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_' False (unat w) =
       sr_ready generated_scheduler_roots (unat w) \<and>
     sr_ready generated_scheduler_roots (unat w)
       \<in> set (p2_physical_roots generated_scheduler_roots) \<and>
     c_guard (sr_ready generated_scheduler_roots (unat w))"
proof -
  have index: "unat w < 4"
    by (rule generated_ready_priority_word_bound[OF bound])
  show ?thesis
    using generated_ready_root_is_array_index
      generated_ready_root_member[OF index]
      generated_ready_root_guard[OF index]
    by blast
qed

text \<open>
  The destination ready queue is a different object from every non-ready
  scheduler root.  Frame proofs for the drain body cite this rather than
  re-deriving separation at a fixed priority.
\<close>

theorem generated_ready_destination_distinct_from_other_roots:
  assumes bound: "(w :: 32 word) < 4"
  shows
    "sr_ready generated_scheduler_roots (unat w) \<noteq>
       sr_delayed_a generated_scheduler_roots \<and>
     sr_ready generated_scheduler_roots (unat w) \<noteq>
       sr_delayed_b generated_scheduler_roots \<and>
     sr_ready generated_scheduler_roots (unat w) \<noteq>
       sr_pending generated_scheduler_roots \<and>
     sr_ready generated_scheduler_roots (unat w) \<noteq>
       sr_suspended generated_scheduler_roots"
proof -
  have index: "unat w < 4"
    by (rule generated_ready_priority_word_bound[OF bound])
  have cases: "unat w = 0 \<or> unat w = 1 \<or> unat w = 2 \<or> unat w = 3"
    using index by linarith
  from cases show ?thesis
    by (elim disjE)
       (simp_all add: generated_scheduler_roots_def
         Scheduler_V611_Parse.pxReadyTasksLists_'_def
         Scheduler_V611_Parse.xDelayedTaskList1_'_def
         Scheduler_V611_Parse.xDelayedTaskList2_'_def
         Scheduler_V611_Parse.xPendingReadyList_'_def
         Scheduler_V611_Parse.xSuspendedTaskList_'_def
         array_ptr_index_def ptr_add_def
         Scheduler_V611_Parse.xLIST_C_size_of)
qed

theorem generated_ready_destination_separated_from_other_roots:
  assumes bound: "(w :: 32 word) < 4"
    and other: "lq \<in> set (p2_physical_roots generated_scheduler_roots)"
    and distinct: "sr_ready generated_scheduler_roots (unat w) \<noteq> lq"
  shows
    "scheduler_list_region (sr_ready generated_scheduler_roots (unat w))
       \<inter> scheduler_list_region lq = {}"
proof -
  have index: "unat w < 4"
    by (rule generated_ready_priority_word_bound[OF bound])
  show ?thesis
    by (rule generated_ready_root_disjoint[OF index other distinct])
qed

end
