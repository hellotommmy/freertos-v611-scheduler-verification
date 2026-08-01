theory List_V611_Raw_R4_Tail_Frame_Post
  imports "EAL6_FreeRTOS_V611_List_Raw_R4_Item_Frame_Post.List_V611_Raw_R4_Item_Frame_Post"
begin

text \<open>
  R4f trailing-eight frame.  First check one arbitrary byte through the five
  source writes; derive the bounded universal without a second VCG.
\<close>

lemma raw_vListRemove_singleton_tail_pointwise:
  assumes tail: "a \<in> {raw_sentinel_tail_addr..+8}"
  shows
    "vListRemove' raw_item_ptr \<bullet>
       (raw_singleton_prestate base d h k owner)
     \<lbrace>\<lambda>r t.
        r = Result () \<and>
        hrs_mem (t_hrs_' t) a =
          hrs_mem
            (t_hrs_' (raw_singleton_prestate base d h k owner)) a
      \<rbrace>"
  unfolding vListRemove'_def
  apply runs_to_vcg
  apply (simp_all only: hrs_mem_update
      raw_item_ptr_guard
      raw_sentinel_ptr_guard
      raw_list_ptr_guard
      raw_singleton_prestate_item_next
      raw_singleton_prestate_item_previous
      raw_singleton_prestate_item_container
      raw_singleton_prestate_index
      raw_singleton_container_cast_back
      raw_singleton_prestate_list_guard
      raw_item_h_val_survives_sentinel_previous_field_update
      raw_item_h_val_survives_sentinel_next_field_update
      raw_list_index_survives_sentinel_previous_field_update
      raw_list_index_survives_sentinel_next_field_update
      raw_sentinel_previous_field_update_tail8_pointwise[OF tail]
      raw_sentinel_next_field_update_tail8_pointwise[OF tail]
      raw_list_update_tail8_pointwise[OF tail]
      raw_item_update_tail8_pointwise[OF tail])
  done

theorem raw_vListRemove_singleton_tail8:
  "vListRemove' raw_item_ptr \<bullet>
     (raw_singleton_prestate base d h k owner)
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      (\<forall>a \<in> {raw_sentinel_tail_addr..+8}.
        hrs_mem (t_hrs_' t) a =
          hrs_mem
            (t_hrs_' (raw_singleton_prestate base d h k owner)) a)
    \<rbrace>"
  apply (subst runs_to_conj)
  apply (rule conjI)
  apply (rule raw_vListRemove_singleton_result)
  apply (simp only: Ball_def)
  apply (rule runs_to_all[THEN iffD2])
  apply (intro allI)
  subgoal for a
    apply (cases "a \<in> {raw_sentinel_tail_addr..+8}")
    apply (rule runs_to_weaken[
      OF raw_vListRemove_singleton_tail_pointwise])
    apply assumption
    apply simp
    apply (rule runs_to_weaken[OF raw_vListRemove_singleton_result])
    apply simp
    done
  done

end
