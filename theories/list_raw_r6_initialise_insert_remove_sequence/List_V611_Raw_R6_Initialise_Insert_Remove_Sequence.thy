theory List_V611_Raw_R6_Initialise_Insert_Remove_Sequence
  imports
    "EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Insert_Sequence.List_V611_Raw_R6_Remove_Insert_Sequence"
begin

text \<open>
  Hard-gate source needle over the untouched generated raw-heap functions.
  The proof composes existing checker-green executions at their actual
  intermediate states; it does not identify an insert result with the
  independently constructed fixed R4 removal prestate, and it does not reopen
  any generated C body.
\<close>

lemma raw_initialised_empty_h_val_cong:
  assumes rel:
    "raw_xlist_rel h raw_list_ptr (raw_empty_abs keys)"
    and list_same:
      "h_val h' raw_list_ptr = h_val h raw_list_ptr"
  shows "raw_xlist_rel h' raw_list_ptr (raw_empty_abs keys)"
  using rel list_same
  by (simp add: raw_xlist_rel_def raw_xlist_view_def raw_empty_abs_def
      raw_cursor_at_def raw_ring_links_def raw_edge_pairs_def
      raw_next_at_def raw_prev_at_def)

lemma raw_empty_relation_keys_cong:
  assumes rel: "raw_xlist_rel h lp (raw_empty_abs keys)"
  shows "raw_xlist_rel h lp (raw_empty_abs keys')"
  using rel
  by (simp add: raw_xlist_rel_def raw_xlist_view_def raw_empty_abs_def
      xlist_wf_def)

lemma raw_vListInitialise_empty_relation:
  "vListInitialise' raw_list_ptr \<bullet> s
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      raw_xlist_rel (hrs_mem (t_hrs_' t)) raw_list_ptr
        (raw_empty_abs keys)
    \<rbrace>"
proof -
  note init = raw_vListInitialise_exact_post[where s=s]
  show ?thesis
    apply (rule runs_to_weaken[OF init])
    apply clarsimp
    apply (rule raw_xlist_rel_emptyI[OF raw_fixed_empty_layout])
    apply (simp_all add: raw_end_item_def)
    done
qed

lemma raw_vListInitialiseItem_preserves_empty_relation:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) raw_list_ptr
       (raw_empty_abs keys)"
  shows
    "vListInitialiseItem' raw_item_ptr \<bullet> s
     \<lbrace>\<lambda>r t.
        r = Result () \<and>
        raw_xlist_rel (hrs_mem (t_hrs_' t)) raw_list_ptr
          (raw_empty_abs keys) \<and>
        pvContainer_C
          (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) = NULL
      \<rbrace>"
proof -
  note init_item =
    raw_vListInitialiseItem_exact_post_and_frames[where s=s]
  show ?thesis
    apply (rule runs_to_weaken[OF init_item])
    apply clarsimp
    apply (rule raw_initialised_empty_h_val_cong[OF rel])
    apply assumption
    done
qed

lemma raw_fixed_fresh_for_initialised_empty:
  "raw_fresh_for_insert raw_list_ptr
     (ring (raw_empty_abs keys)) raw_item_ptr"
  using raw_item_ptr_guard raw_fixed_item_list_regions_disjoint
  by (simp add: raw_fresh_for_insert_def raw_empty_abs_def
      raw_end_item_def raw_item_ptr_def)

lemma raw_initialised_empty_count_can_increment:
  "raw_count_can_increment (raw_empty_abs keys)"
  by (simp add: raw_count_can_increment_def raw_empty_abs_def)

lemma raw_empty_insert_end_remove_roundtrip[simp]:
  "list_remove_abs p
      (list_insert_end_abs p k (raw_empty_abs keys)) =
    raw_empty_abs (keys(p := k))"
  by (simp add: list_remove_abs_def list_insert_end_abs_def
      raw_empty_abs_def)

definition raw_initialise_insert_remove_needle' where
  "raw_initialise_insert_remove_needle' =
     bind (vListInitialise' raw_list_ptr) (\<lambda>_.
       bind (vListInitialiseItem' raw_item_ptr) (\<lambda>_.
         bind (vListInsertEnd' raw_list_ptr raw_item_ptr) (\<lambda>_.
           vListRemove' raw_item_ptr)))"

theorem raw_vListInitialise_insert_end_remove_refines:
  "raw_initialise_insert_remove_needle' \<bullet> s
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      (\<exists>k.
        raw_xlist_rel (hrs_mem (t_hrs_' t)) raw_list_ptr
          (list_remove_abs raw_item_ptr
            (list_insert_end_abs raw_item_ptr k
              (raw_empty_abs keys))))
    \<rbrace>"
  unfolding raw_initialise_insert_remove_needle'_def
  apply (rule runs_to_bind)
  apply (rule runs_to_weaken[OF
        raw_vListInitialise_empty_relation[where s=s and keys=keys]])
  apply clarsimp
  apply (rule runs_to_bind)
  apply (rule runs_to_weaken)
   apply (rule raw_vListInitialiseItem_preserves_empty_relation)
   apply assumption
  apply clarsimp
  apply (rule runs_to_bind)
  apply (rule runs_to_weaken)
   apply (rule raw_vListInsertEnd_general_refines_via_transformer)
     apply assumption
    apply (rule raw_fixed_fresh_for_initialised_empty)
   apply (rule raw_initialised_empty_count_can_increment)
  apply clarsimp
  apply (rule runs_to_weaken)
   apply (rule raw_vListRemove_general_refines)
    apply assumption
   apply (simp add: list_insert_end_abs_def raw_empty_abs_def)
  apply auto
  done

corollary raw_vListInitialise_insert_end_remove_empty_refines:
  "raw_initialise_insert_remove_needle' \<bullet> s
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      raw_xlist_rel (hrs_mem (t_hrs_' t)) raw_list_ptr
        (raw_empty_abs keys)
    \<rbrace>"
proof -
  note sequence = raw_vListInitialise_insert_end_remove_refines[
    where s=s and keys=keys]
  show ?thesis
    apply (rule runs_to_weaken[OF sequence])
    apply clarsimp
    apply (rule raw_empty_relation_keys_cong)
    apply assumption
    done
qed

end
