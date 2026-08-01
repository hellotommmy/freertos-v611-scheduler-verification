theory List_V611_Raw_R6_Insert_Source_Effects
  imports "EAL6_FreeRTOS_V611_List_Raw_R6_Unlink_Projection.List_V611_Raw_R6_Unlink_Projection"
begin

text \<open>
  One auditable raw-byte transformer for the seven writes performed by
  vListInsertEnd.  The four link writes are field-precise, including when the
  old cursor or its successor is the embedded mini-sentinel.  The list-index,
  container, and count stages retain the whole-structure update shape emitted
  by the raw AutoCorres translation.
\<close>

definition raw_insert_next_heap ::
  "heap_mem \<Rightarrow> raw_node_id \<Rightarrow> raw_node_id \<Rightarrow> heap_mem"
where
  "raw_insert_next_heap h u v =
     heap_update (raw_next_field_ptr u) v h"

definition raw_insert_previous_heap ::
  "heap_mem \<Rightarrow> raw_node_id \<Rightarrow> raw_node_id \<Rightarrow> heap_mem"
where
  "raw_insert_previous_heap h u v =
     heap_update (raw_previous_field_ptr u) v h"

definition raw_insert_index_heap ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow> heap_mem"
where
  "raw_insert_index_heap h lp p =
     heap_update lp
       (pxIndex_C_update (\<lambda>_. p) (h_val h lp)) h"

definition raw_insert_container_heap ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow> heap_mem"
where
  "raw_insert_container_heap h lp p =
     heap_update p
       (pvContainer_C_update
         (\<lambda>_. PTR_COERCE(xLIST_C \<rightarrow> unit) lp)
         (h_val h p)) h"

definition raw_insert_count_heap ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> heap_mem"
where
  "raw_insert_count_heap h lp =
     heap_update lp
       (uxNumberOfItems_C_update (\<lambda>n. n + 1) (h_val h lp)) h"

definition raw_insert_concrete_heap ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow> raw_node_id \<Rightarrow> heap_mem"
where
  "raw_insert_concrete_heap h lp xs p =
     (let c = raw_cursor_node lp xs;
          q = raw_next_at h lp c;
          h1 = raw_insert_next_heap h p q;
          h2 = raw_insert_previous_heap h1 p c;
          h3 = raw_insert_previous_heap h2 q p;
          h4 = raw_insert_next_heap h3 c p;
          h5 = raw_insert_index_heap h4 lp p;
          h6 = raw_insert_container_heap h5 lp p
      in raw_insert_count_heap h6 lp)"

lemma raw_insert_next_heap_preserves_list:
  assumes fresh: "raw_fresh_for_insert lp rs p"
  shows
    "h_val (raw_insert_next_heap h p q) lp = h_val h lp"
proof -
  have item_list:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have field_list:
    "raw_pointer_field_region (raw_next_field_ptr p) \<inter>
     raw_list_region lp = {}"
    using raw_next_field_region_subset_item[where u=p] item_list by blast
  show ?thesis
    unfolding raw_insert_next_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_list[OF field_list])
qed

lemma raw_insert_two_link_heaps_cursor_next:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "xLIST_ITEM_C.pxNext_C
       (h_val
         (raw_insert_previous_heap
           (raw_insert_next_heap h p q) p
           (raw_cursor_node lp xs))
         (raw_cursor_node lp xs)) =
     raw_next_at h lp (raw_cursor_node lp xs)"
proof -
  let ?c = "raw_cursor_node lp xs"
  let ?h1 = "raw_insert_next_heap h p q"
  let ?h2 = "raw_insert_previous_heap ?h1 p ?c"
  have old_wf: "xlist_wf xs"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have c_member:
    "?c \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_cursor_node_in_cycle[OF old_wf])
  have p_guard: "c_guard p"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have h1_whole:
    "?h1 =
     heap_update p
       (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. q) (h_val h p)) h"
    unfolding raw_insert_next_heap_def
    by (rule raw_next_field_update_to_whole[OF p_guard])
  have h2_whole:
    "?h2 =
     heap_update p
       (xLIST_ITEM_C.pxPrevious_C_update (\<lambda>_. ?c) (h_val ?h1 p))
       ?h1"
    unfolding raw_insert_previous_heap_def
    by (rule raw_previous_field_update_to_whole[OF p_guard])
  have stable0:
    "xLIST_ITEM_C.pxNext_C
       (h_val
         (heap_update p
           (xLIST_ITEM_C.pxPrevious_C_update
             (\<lambda>_. ?c) (h_val ?h1 p))
           (heap_update p
             (xLIST_ITEM_C.pxNext_C_update
               (\<lambda>_. q) (h_val h p)) h))
         ?c) =
     xLIST_ITEM_C.pxNext_C (h_val h ?c)"
    by (rule raw_fresh_two_item_updates_preserve_cycle_next[
          OF layout fresh c_member])
  have stable:
    "xLIST_ITEM_C.pxNext_C (h_val ?h2 ?c) =
     xLIST_ITEM_C.pxNext_C (h_val h ?c)"
    using stable0 h1_whole h2_whole by simp
  have initial:
    "xLIST_ITEM_C.pxNext_C (h_val h ?c) = raw_next_at h lp ?c"
    by (rule raw_full_next_is_sentinel_safe)
  show ?thesis using stable initial by simp
qed

text \<open>
  This is the only new symbolic execution of vListInsertEnd.  Its postcondition
  deliberately records only exact raw memory.  Normal return is conjoined from
  the already checked general-result theorem below, so later projections must
  not reopen the generated body.
\<close>

lemma raw_vListInsertEnd_general_heap_only:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "vListInsertEnd' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       hrs_mem (t_hrs_' t) =
         raw_insert_concrete_heap (hrs_mem (t_hrs_' s)) lp xs p
     \<rbrace>"
proof -
  let ?h = "hrs_mem (t_hrs_' s)"
  let ?c = "raw_cursor_node lp xs"
  let ?q = "raw_next_at ?h lp ?c"
  have old_wf: "xlist_wf xs"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have c_member:
    "?c \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_cursor_node_in_cycle[OF old_wf])
  have p_guard: "c_guard p"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have c_guard: "c_guard ?c"
    by (rule raw_xlist_rel_cycle_node_guard[OF rel c_member])
  have index_eq:
    "pxIndex_C (h_val ?h lp) = ?c"
    by (rule raw_xlist_rel_index_eq_cursor_node[OF rel])
  have initial_next:
    "xLIST_ITEM_C.pxNext_C (h_val ?h ?c) = ?q"
    by (rule raw_full_next_is_sentinel_safe)
  have first_list:
    "h_val (raw_insert_next_heap ?h p ?q) lp = h_val ?h lp"
    by (rule raw_insert_next_heap_preserves_list[OF fresh])
  have prefix_next:
    "xLIST_ITEM_C.pxNext_C
       (h_val
         (raw_insert_previous_heap
           (raw_insert_next_heap ?h p ?q) p ?c) ?c) = ?q"
    by (rule raw_insert_two_link_heaps_cursor_next[OF rel fresh])
  show ?thesis
    unfolding vListInsertEnd'_def
    apply runs_to_vcg
    apply (simp_all only: hrs_mem_update)
    apply ((rule
        raw_general_insert_index_next_guard_after_item_updates[OF rel fresh]
      | rule raw_general_insert_index_guard[OF rel fresh]
      | rule raw_general_insert_list_guard[OF rel fresh]
      | rule raw_general_insert_item_guard[OF rel fresh])+)
    apply (simp_all only: index_eq initial_next)
    apply (simp_all only:
        raw_next_field_update_to_whole[OF p_guard, symmetric]
        raw_previous_field_update_to_whole[OF p_guard, symmetric]
        raw_next_field_update_to_whole[OF c_guard, symmetric])
    apply (fold raw_previous_field_ptr_def)
    apply (fold raw_insert_next_heap_def raw_insert_previous_heap_def)
    apply (simp_all only: first_list prefix_next index_eq)
    apply (fold raw_insert_index_heap_def)
    apply (fold raw_insert_container_heap_def)
    apply (fold raw_insert_count_heap_def)
    apply (simp_all add: raw_insert_concrete_heap_def Let_def)
    done
qed

theorem raw_vListInsertEnd_general_heap_effect:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "vListInsertEnd' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       hrs_mem (t_hrs_' t) =
         raw_insert_concrete_heap (hrs_mem (t_hrs_' s)) lp xs p
     \<rbrace>"
proof -
  note result = raw_vListInsertEnd_general_result[OF rel fresh]
  note heap = raw_vListInsertEnd_general_heap_only[OF rel fresh]
  show ?thesis using result heap by (simp only: runs_to_conj)
qed

end
