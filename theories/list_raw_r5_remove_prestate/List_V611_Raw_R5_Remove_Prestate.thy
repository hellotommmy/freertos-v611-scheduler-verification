theory List_V611_Raw_R5_Remove_Prestate
  imports
    "EAL6_FreeRTOS_V611_List_Raw_R5_Interface.List_V611_Raw_R5_Interface"
    "EAL6_FreeRTOS_V611_List_Raw_R4_Prestate.List_V611_Raw_R4_Prestate"
begin

text \<open>
  Semantic input bridge for the fixed singleton-removal needle.  This theory
  is independent of the vListRemove body: it proves that the separately
  encoded R4 singleton state has a non-vacuous abstract preimage.
\<close>

lemma raw_singleton_remove_abs[simp]:
  "list_remove_abs p (raw_singleton_abs p keys k) =
   raw_empty_abs (keys(p := k))"
  by (simp add: raw_singleton_abs_def raw_empty_abs_def
      list_insert_end_abs_def list_remove_abs_def)

lemma raw_singleton_prestate_rep:
  "raw_xlist_rel
     (hrs_mem (t_hrs_' (raw_singleton_prestate base d h k owner)))
     raw_list_ptr (raw_singleton_abs raw_item_ptr keys k)"
proof -
  note fields = raw_singleton_prestate_fields[
    where base=base and d=d and h=h and k=k and owner=owner]
  show ?thesis
    apply (rule raw_xlist_rel_singletonI)
    apply (rule raw_fixed_singleton_layout)
    using fields
    apply (simp_all add: raw_singleton_fields_def
        raw_singleton_heap_fields_def raw_end_item_def)
    done
qed

end
