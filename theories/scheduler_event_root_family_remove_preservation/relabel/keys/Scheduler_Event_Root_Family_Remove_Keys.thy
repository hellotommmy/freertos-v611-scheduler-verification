theory Scheduler_Event_Root_Family_Remove_Keys
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Cursor.Scheduler_Event_Root_Family_Remove_Cursor"
begin

lemma xlist_relabel_remove_keys_preserved:
  assumes relabel: "xlist_relabel D rx ax"
  shows
    "\<forall>q \<in> set (ring (list_remove_abs p rx)). \<forall>m.
       D q = Some m \<longrightarrow>
       item_key (list_remove_abs p rx) q =
         item_key (list_remove_abs n ax) m"
proof (intro ballI allI impI)
  fix q m
  assume q_post: "q \<in> set (ring (list_remove_abs p rx))"
    and q_decode: "D q = Some m"
  have q_removed: "q \<in> set (remove1 p (ring rx))"
    using q_post by (simp add: list_remove_abs_def)
  have q_pre: "q \<in> set (ring rx)"
    by (rule set_remove1_subset[THEN subsetD, OF q_removed])
  have key_pre: "item_key rx q = item_key ax m"
    by (rule xlist_relabel_key_agreementD[
          OF relabel q_pre q_decode])
  show
    "item_key (list_remove_abs p rx) q =
     item_key (list_remove_abs n ax) m"
    using key_pre by (simp add: list_remove_abs_def)
qed

end
