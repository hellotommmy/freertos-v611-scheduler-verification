theory Scheduler_Resume_Generated_Ready_Array_ABI
  imports
    "EAL6_FreeRTOS_V611_Scheduler_XList_Relabel_Insert_End.Scheduler_XList_Relabel_Insert_End"
    "EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Static_Layout.Scheduler_P2_Frozen_Static_Layout"
begin

lemma generated_ready_array_guard:
  "c_guard Scheduler_V611_Parse.pxReadyTasksLists_'"
proof -
  have no_wrap:
    "unat (0x00102020 :: addr) + 80 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have membership:
    "((0 :: addr) \<in> {(0x00102020 :: addr)..+80}) =
      (unat (0x00102020 :: addr) \<le> unat (0 :: addr) \<and>
       unat (0 :: addr) < unat (0x00102020 :: addr) + 80)"
    by (rule intvl_no_overflow_nat[OF no_wrap])
  have no_null: "(0 :: addr) \<notin> {(0x00102020 :: addr)..+80}"
    using membership by simp
  show ?thesis
    unfolding Scheduler_V611_Parse.pxReadyTasksLists_'_def
    using no_null
    by (simp add: c_guard_def c_null_guard_def ptr_aligned_def
        align_of_def align_td_array size_of_def size_td_array)
qed

end
