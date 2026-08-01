theory List_V611_Raw_R3_Tail_Frame_Post
  imports "EAL6_FreeRTOS_V611_List_Raw_R3_Tail_Frame.List_V611_Raw_R3_Tail_Frame"
begin

text \<open>
  First export tail preservation for one arbitrary address in the tail.  The
  bounded universal postcondition is derived only after this VCG is green.
\<close>

lemma raw_vListInsertEnd_empty_tail_pointwise:
  assumes tail: "a \<in> {raw_sentinel_tail_addr..+8}"
  shows
    "vListInsertEnd' raw_list_ptr raw_item_ptr \<bullet>
       (raw_insert_end_prestate base d h k owner)
     \<lbrace>\<lambda>r t.
        r = Result () \<and>
        hrs_mem (t_hrs_' t) a =
          hrs_mem
            (t_hrs_' (raw_insert_end_prestate base d h k owner)) a
      \<rbrace>"
  unfolding vListInsertEnd'_def
  apply runs_to_vcg
  apply (rule raw_insert_end_prestate_index_guard)
  apply (simp only: hrs_mem_update)
  apply (rule raw_prestate_index_next_guard_after_item_updates)
  apply (simp_all only: hrs_mem_update
      raw_insert_end_prestate_index
      raw_sentinel_h_val_after_item_update_direct
      raw_insert_end_prestate_sentinel_next_raw
      raw_list_update_tail8_pointwise[OF tail]
      raw_item_update_tail8_pointwise[OF tail]
      raw_sentinel_previous_field_update_tail8_pointwise[OF tail]
      raw_sentinel_whole_next_update_tail8_pointwise[OF tail])
  done

lemma raw_vListInsertEnd_empty_tail8:
  "vListInsertEnd' raw_list_ptr raw_item_ptr \<bullet>
     (raw_insert_end_prestate base d h k owner)
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      (\<forall>a \<in> {raw_sentinel_tail_addr..+8}.
        hrs_mem (t_hrs_' t) a =
          hrs_mem
            (t_hrs_' (raw_insert_end_prestate base d h k owner)) a)
    \<rbrace>"
  apply (subst runs_to_conj)
  apply (rule conjI)
  apply (rule raw_vListInsertEnd_empty_result)
  apply (simp only: Ball_def)
  apply (rule runs_to_all[THEN iffD2])
  apply (intro allI)
  subgoal for a
    apply (cases "a \<in> {raw_sentinel_tail_addr..+8}")
    apply (rule runs_to_weaken[
      OF raw_vListInsertEnd_empty_tail_pointwise])
    apply assumption
    apply simp
    apply (rule runs_to_weaken[OF raw_vListInsertEnd_empty_result])
    apply simp
    done
  done

end
