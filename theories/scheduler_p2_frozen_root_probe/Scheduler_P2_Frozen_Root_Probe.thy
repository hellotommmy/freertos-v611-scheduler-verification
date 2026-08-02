theory Scheduler_P2_Frozen_Root_Probe
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Generated_Layout_First.Scheduler_P2_Generated_Layout_First"
begin

text \<open>
  G1: a single artifact-bound root.  Unlike the rejected descendant
  specification experiment, this equation is the ordinary definition that
  CParser installed while translating the frozen scheduler build.
\<close>

lemma frozen_delayed_a_pointer [simp]:
  "Scheduler_V611_Parse.xDelayedTaskList1_' =
     (Ptr 0x0010208c :: Scheduler_V611_Parse.xLIST_C ptr)"
  by (simp add: Scheduler_V611_Parse.xDelayedTaskList1_'_def)

lemma frozen_delayed_a_no_null_interval:
  "(0 :: addr) \<notin> {0x0010208c..+20}"
proof -
  have no_wrap: "unat (0x0010208c :: addr) + 20 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have membership:
    "((0 :: addr) \<in> {0x0010208c..+20}) =
      (unat (0x0010208c :: addr) \<le> unat (0 :: addr) \<and>
       unat (0 :: addr) < unat (0x0010208c :: addr) + 20)"
    by (rule intvl_no_overflow_nat[OF no_wrap])
  from membership show ?thesis by simp
qed

lemma frozen_delayed_a_guard:
  "c_guard Scheduler_V611_Parse.xDelayedTaskList1_'"
  by (simp add: c_guard_def c_null_guard_def ptr_aligned_def align_of_def
      size_of_def frozen_delayed_a_no_null_interval)

end
