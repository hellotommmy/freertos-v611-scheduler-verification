theory Scheduler_Insert_End_Translation_General
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Ordered_Insert_General_Loop.Scheduler_Ordered_Insert_General_Loop"
    "EAL6_FreeRTOS_V611_List_Insert_End_Generated_Capstone.List_Insert_End_Generated_Capstone"
begin

text \<open>
  Scheduler-translation Gate-L for vListInsertEnd.  This theory opens the
  generated scheduler body rather than identifying it with the separately
  translated list.c body.  All addresses, list contents, cursor positions,
  item keys, and source states remain quantified.  In particular, the empty
  ring (where cursor and successor are the same sentinel) is not split out or
  excluded.
\<close>

definition scheduler_insert_index_heap ::
  "heap_mem \<Rightarrow> Scheduler_V611_Parse.xLIST_C ptr \<Rightarrow>
   Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow> heap_mem"
where
  "scheduler_insert_index_heap h lp p =
     heap_update lp
       (Scheduler_V611_Parse.xLIST_C.pxIndex_C_update
         (\<lambda>_. p) (h_val h lp)) h"

lemma scheduler_insert_index_heap_abi:
  assumes guard: "c_guard lp"
  shows
    "scheduler_insert_index_heap h lp p =
     raw_insert_index_heap h (abi_list_ptr lp) (abi_item_ptr p)"
  unfolding scheduler_insert_index_heap_def raw_insert_index_heap_def
  by (rule abi_list_index_whole_write[OF guard])

definition scheduler_insert_end_general_heap ::
  "heap_mem \<Rightarrow> Scheduler_V611_Parse.xLIST_C ptr \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow>
   Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow> heap_mem"
where
  "scheduler_insert_end_general_heap h lp xs p =
     (let c = scheduler_item_of_raw
            (raw_cursor_node (abi_list_ptr lp) xs);
          q = Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h c);
          h1 = scheduler_insert_next_heap h p q;
          h2 = scheduler_insert_previous_heap h1 p c;
          h3 = scheduler_insert_previous_heap h2 q p;
          h4 = scheduler_insert_next_heap h3 c p;
          h5 = scheduler_insert_index_heap h4 lp p;
          h6 = scheduler_insert_container_heap h5 lp p
      in scheduler_insert_count_heap h6 lp)"

lemma scheduler_insert_end_general_heap_abi:
  assumes item_guard: "c_guard p"
    and list_guard: "c_guard lp"
  shows
    "scheduler_insert_end_general_heap h lp xs p =
     raw_insert_concrete_heap h (abi_list_ptr lp) xs (abi_item_ptr p)"
proof -
  have next_abi:
    "abi_item_ptr
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val h (scheduler_item_of_raw u))) =
     raw_next_at h (abi_list_ptr lp) u" for u
    by (rule scheduler_item_next_abi_raw)
  show ?thesis
    unfolding scheduler_insert_end_general_heap_def
      raw_insert_concrete_heap_def Let_def
    by (simp only:
        next_abi abi_item_ptr_scheduler_item_of_raw
        scheduler_insert_next_heap_abi
        scheduler_insert_previous_heap_abi
        scheduler_insert_index_heap_abi[OF list_guard]
        scheduler_insert_container_heap_abi[OF item_guard]
        scheduler_insert_count_heap_abi[OF list_guard])
qed

lemma scheduler_insert_index_state_update_to_whole:
  "(\<lambda>(a :: heap_raw_state). hrs_mem_update
     (heap_update lp
       (Scheduler_V611_Parse.xLIST_C.pxIndex_C_update
         (\<lambda>_. p) (h_val (hrs_mem a) lp))) a) =
   (\<lambda>(a :: heap_raw_state). hrs_mem_update
     (\<lambda>h. scheduler_insert_index_heap h lp p) a)"
  apply (rule ext)
  subgoal for a
    apply (cases a)
    apply (simp add: hrs_mem_update_def hrs_mem_def
        scheduler_insert_index_heap_def)
    done
  done

lemma scheduler_insert_end_index_exact:
  assumes rel: "raw_xlist_rel h (abi_list_ptr lp) xs"
  shows
    "Scheduler_V611_Parse.xLIST_C.pxIndex_C (h_val h lp) =
     scheduler_item_of_raw (raw_cursor_node (abi_list_ptr lp) xs)"
proof -
  have raw:
    "List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C
       (h_val h (abi_list_ptr lp)) =
     raw_cursor_node (abi_list_ptr lp) xs"
    by (rule raw_xlist_rel_index_eq_cursor_node[OF rel])
  have abi:
    "List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C
       (h_val h (abi_list_ptr lp)) =
     abi_item_ptr
       (Scheduler_V611_Parse.xLIST_C.pxIndex_C (h_val h lp))"
    by (rule abi_list_index_h_val)
  show ?thesis
    apply (rule iffD1[OF abi_item_ptr_eq_iff])
    using raw abi by simp
qed

lemma scheduler_item_update_preserves_disjoint_raw_list:
  assumes disjoint:
    "raw_item_region (abi_item_ptr p) \<inter> raw_list_region lp = {}"
  shows
    "h_val
       (heap_update p (v :: Scheduler_V611_Parse.xLIST_ITEM_C) h) lp =
     h_val h lp"
proof -
  have byte_disjoint:
    "{ptr_val p..+
       length (to_bytes v
         (heap_list h
           (size_of TYPE(Scheduler_V611_Parse.xLIST_ITEM_C))
           (ptr_val p)))} \<inter>
     {ptr_val lp..+
       size_of TYPE(List_V611_Raw_Skip_Translation.xLIST_C)} = {}"
    using disjoint
    by (simp add: raw_item_region_def raw_list_region_def
        abi_item_ptr_def abi_xLIST_ITEM_C_size)
  have heap_lists_same:
    "heap_list
       (heap_update_list (ptr_val p)
         (to_bytes v
           (heap_list h
             (size_of TYPE(Scheduler_V611_Parse.xLIST_ITEM_C))
             (ptr_val p))) h)
       (size_of TYPE(List_V611_Raw_Skip_Translation.xLIST_C))
       (ptr_val lp) =
     heap_list h
       (size_of TYPE(List_V611_Raw_Skip_Translation.xLIST_C))
       (ptr_val lp)"
    by (rule heap_list_update_disjoint_same[OF byte_disjoint])
  show ?thesis
    unfolding h_val_def heap_update_def
    using heap_lists_same by simp
qed

lemma scheduler_item_update_preserves_disjoint_raw_item:
  assumes disjoint:
    "raw_item_region (abi_item_ptr p) \<inter> raw_item_region u = {}"
  shows
    "h_val
       (heap_update p (v :: Scheduler_V611_Parse.xLIST_ITEM_C) h) u =
     h_val h u"
proof -
  have byte_disjoint:
    "{ptr_val p..+
       length (to_bytes v
         (heap_list h
           (size_of TYPE(Scheduler_V611_Parse.xLIST_ITEM_C))
           (ptr_val p)))} \<inter>
     {ptr_val u..+
       size_of TYPE(List_V611_Raw_Skip_Translation.xLIST_ITEM_C)} = {}"
    using disjoint
    by (simp add: raw_item_region_def abi_item_ptr_def
        abi_xLIST_ITEM_C_size)
  have heap_lists_same:
    "heap_list
       (heap_update_list (ptr_val p)
         (to_bytes v
           (heap_list h
             (size_of TYPE(Scheduler_V611_Parse.xLIST_ITEM_C))
             (ptr_val p))) h)
       (size_of TYPE(List_V611_Raw_Skip_Translation.xLIST_ITEM_C))
       (ptr_val u) =
     heap_list h
       (size_of TYPE(List_V611_Raw_Skip_Translation.xLIST_ITEM_C))
       (ptr_val u)"
    by (rule heap_list_update_disjoint_same[OF byte_disjoint])
  show ?thesis
    unfolding h_val_def heap_update_def
    using heap_lists_same by simp
qed

lemma scheduler_fresh_item_update_preserves_cycle_next:
  assumes layout: "raw_xlist_layout (abi_list_ptr lp) rs"
    and fresh:
      "raw_fresh_for_insert (abi_list_ptr lp) rs
        (abi_item_ptr p)"
    and cycle:
      "u \<in> insert (raw_end_item (abi_list_ptr lp)) (set rs)"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
       (h_val
         (heap_update p (v :: Scheduler_V611_Parse.xLIST_ITEM_C) h)
         (scheduler_item_of_raw u)) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
       (h_val h (scheduler_item_of_raw u))"
proof (cases "u = raw_end_item (abi_list_ptr lp)")
  case True
  have disjoint:
    "raw_item_region (abi_item_ptr p) \<inter>
     raw_list_region (abi_list_ptr lp) = {}"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have list_same:
    "h_val (heap_update p v h) (abi_list_ptr lp) =
     h_val h (abi_list_ptr lp)"
    by (rule scheduler_item_update_preserves_disjoint_raw_list[OF
          disjoint])
  have raw_next_same:
    "raw_next_at (heap_update p v h) (abi_list_ptr lp) u =
     raw_next_at h (abi_list_ptr lp) u"
    using True list_same by (simp add: raw_next_at_def)
  have after:
    "abi_item_ptr
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val (heap_update p v h) (scheduler_item_of_raw u))) =
     raw_next_at (heap_update p v h) (abi_list_ptr lp) u"
    by (rule scheduler_item_next_abi_raw)
  have before:
    "abi_item_ptr
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val h (scheduler_item_of_raw u))) =
     raw_next_at h (abi_list_ptr lp) u"
    by (rule scheduler_item_next_abi_raw)
  show ?thesis
    apply (rule iffD1[OF abi_item_ptr_eq_iff])
    using after before raw_next_same by simp
next
  case False
  have live: "u \<in> set rs"
    using cycle False by simp
  have disjoint:
    "raw_item_region (abi_item_ptr p) \<inter> raw_item_region u = {}"
    using fresh live by (simp add: raw_fresh_for_insert_def)
  have item_same:
    "h_val (heap_update p v h) u = h_val h u"
    by (rule scheduler_item_update_preserves_disjoint_raw_item[OF
          disjoint])
  have raw_next_same:
    "raw_next_at (heap_update p v h) (abi_list_ptr lp) u =
     raw_next_at h (abi_list_ptr lp) u"
    using False item_same by (simp add: raw_next_at_def)
  have after:
    "abi_item_ptr
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val (heap_update p v h) (scheduler_item_of_raw u))) =
     raw_next_at (heap_update p v h) (abi_list_ptr lp) u"
    by (rule scheduler_item_next_abi_raw)
  have before:
    "abi_item_ptr
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val h (scheduler_item_of_raw u))) =
     raw_next_at h (abi_list_ptr lp) u"
    by (rule scheduler_item_next_abi_raw)
  show ?thesis
    apply (rule iffD1[OF abi_item_ptr_eq_iff])
    using after before raw_next_same by simp
qed

lemma scheduler_fresh_two_item_updates_preserve_cycle_next:
  assumes rel: "raw_xlist_rel h (abi_list_ptr lp) xs"
    and fresh:
      "raw_fresh_for_insert (abi_list_ptr lp) (ring xs)
        (abi_item_ptr p)"
    and cycle:
      "u \<in> insert (raw_end_item (abi_list_ptr lp)) (set (ring xs))"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
       (h_val
         (heap_update p (v2 :: Scheduler_V611_Parse.xLIST_ITEM_C)
           (heap_update p (v1 :: Scheduler_V611_Parse.xLIST_ITEM_C) h))
         (scheduler_item_of_raw u)) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
       (h_val h (scheduler_item_of_raw u))"
proof -
  have layout: "raw_xlist_layout (abi_list_ptr lp) (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have first:
    "Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
       (h_val (heap_update p v1 h) (scheduler_item_of_raw u)) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
       (h_val h (scheduler_item_of_raw u))"
    by (rule scheduler_fresh_item_update_preserves_cycle_next[OF
          layout fresh cycle])
  have second:
    "Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
       (h_val (heap_update p v2 (heap_update p v1 h))
         (scheduler_item_of_raw u)) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
       (h_val (heap_update p v1 h) (scheduler_item_of_raw u))"
    by (rule scheduler_fresh_item_update_preserves_cycle_next[OF
          layout fresh cycle])
  show ?thesis using first second by simp
qed

lemma scheduler_insert_end_successor_guard_after_item_updates:
  assumes rel:
      "raw_xlist_rel
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
        (abi_list_ptr lp) xs"
    and fresh:
      "raw_fresh_for_insert (abi_list_ptr lp) (ring xs)
        (abi_item_ptr p)"
  shows
    "c_guard
      (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
        (h_val
          (heap_update p (v2 :: Scheduler_V611_Parse.xLIST_ITEM_C)
            (heap_update p (v1 :: Scheduler_V611_Parse.xLIST_ITEM_C)
              (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))))
          (Scheduler_V611_Parse.xLIST_C.pxIndex_C
            (h_val
              (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)) lp))))"
proof -
  let ?h =
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)"
  let ?rc = "raw_cursor_node (abi_list_ptr lp) xs"
  let ?c = "scheduler_item_of_raw ?rc"
  have wf: "xlist_wf xs"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have rc_cycle:
    "?rc \<in> insert (raw_end_item (abi_list_ptr lp)) (set (ring xs))"
    by (rule raw_cursor_node_in_cycle[OF wf])
  have stable:
    "Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
       (h_val (heap_update p v2 (heap_update p v1 ?h)) ?c) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val ?h ?c)"
    by (rule scheduler_fresh_two_item_updates_preserve_cycle_next[
          OF rel fresh rc_cycle])
  have next_exact:
    "Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val ?h ?c) =
     scheduler_item_of_raw
       (raw_next_at ?h (abi_list_ptr lp) ?rc)"
    by (rule scheduler_item_next_is_raw_successor)
  have next_guard:
    "c_guard
      (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val ?h ?c))"
    using scheduler_cycle_successor_guard[OF rel rc_cycle] next_exact
    by simp
  have index:
    "Scheduler_V611_Parse.xLIST_C.pxIndex_C (h_val ?h lp) = ?c"
    by (rule scheduler_insert_end_index_exact[OF rel])
  show ?thesis using stable next_guard index by simp
qed

theorem scheduler_vListInsertEnd_general_exact_state:
  fixes s :: Scheduler_V611_Parse.globals
    and lp :: "Scheduler_V611_Parse.xLIST_C ptr"
    and p :: "Scheduler_V611_Parse.xLIST_ITEM_C ptr"
  assumes rel:
      "raw_xlist_rel
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
        (abi_list_ptr lp) xs"
    and fresh:
      "raw_fresh_for_insert (abi_list_ptr lp) (ring xs)
        (abi_item_ptr p)"
  shows
    "Scheduler_V611_Delay_Translation.vListInsertEnd' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_mem_state
         (raw_insert_concrete_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
           (abi_list_ptr lp) xs (abi_item_ptr p)) s
     \<rbrace>"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)"
  let ?rc = "raw_cursor_node (abi_list_ptr lp) xs"
  let ?c = "scheduler_item_of_raw ?rc"
  let ?rq = "raw_next_at ?h (abi_list_ptr lp) ?rc"
  let ?q = "scheduler_item_of_raw ?rq"
  have wf: "xlist_wf xs"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have rc_cycle:
    "?rc \<in> insert (raw_end_item (abi_list_ptr lp)) (set (ring xs))"
    by (rule raw_cursor_node_in_cycle[OF wf])
  have links: "raw_ring_links ?h (abi_list_ptr lp) (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have rq_cycle:
    "?rq \<in> insert (raw_end_item (abi_list_ptr lp)) (set (ring xs))"
    by (rule raw_ring_links_next_closed[OF links rc_cycle])
  have p_guard: "c_guard p"
  proof -
    have "c_guard (abi_item_ptr p)"
      using fresh by (simp add: raw_fresh_for_insert_def)
    then show ?thesis by (rule iffD1[OF abi_item_ptr_c_guard])
  qed
  have lp_guard: "c_guard lp"
  proof -
    have "c_guard (abi_list_ptr lp)"
      using rel by (simp add: raw_xlist_rel_def raw_xlist_layout_def)
    then show ?thesis by (rule iffD1[OF abi_list_ptr_c_guard])
  qed
  have c_guard: "c_guard ?c"
    by (rule scheduler_cycle_node_guard[OF rel rc_cycle])
  have q_guard: "c_guard ?q"
    by (rule scheduler_cycle_node_guard[OF rel rq_cycle])
  have index: "Scheduler_V611_Parse.xLIST_C.pxIndex_C (h_val ?h lp) = ?c"
    by (rule scheduler_insert_end_index_exact[OF rel])
  have next_eq:
    "Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val ?h ?c) = ?q"
    by (rule scheduler_item_next_is_raw_successor)
  have read_after_next:
    "h_val (scheduler_insert_next_heap h p q) p =
     Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C_update
       (\<lambda>_. q) (h_val h p)" for h q
    apply (subst scheduler_next_field_update_to_whole[OF p_guard])
    using p_guard by (simp add: h_val_heap_update)
  have index_after_next:
    "Scheduler_V611_Parse.xLIST_C.pxIndex_C
       (h_val (scheduler_insert_next_heap h p q) lp) =
     Scheduler_V611_Parse.xLIST_C.pxIndex_C (h_val h lp)" for h q
  proof -
    have raw_frame:
      "h_val (scheduler_insert_next_heap h p q) (abi_list_ptr lp) =
       h_val h (abi_list_ptr lp)"
      apply (simp only: scheduler_insert_next_heap_abi)
      by (rule raw_insert_next_heap_preserves_list[OF fresh])
    have after:
      "List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C
         (h_val (scheduler_insert_next_heap h p q) (abi_list_ptr lp)) =
       abi_item_ptr
         (Scheduler_V611_Parse.xLIST_C.pxIndex_C
           (h_val (scheduler_insert_next_heap h p q) lp))"
      by (rule abi_list_index_h_val)
    have before:
      "List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C
         (h_val h (abi_list_ptr lp)) =
       abi_item_ptr
         (Scheduler_V611_Parse.xLIST_C.pxIndex_C (h_val h lp))"
      by (rule abi_list_index_h_val)
    show ?thesis
      apply (rule iffD1[OF abi_item_ptr_eq_iff])
      using raw_frame after before by simp
  qed
  have prefix_unchanged:
    "Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
       (h_val
         (scheduler_insert_previous_heap
           (scheduler_insert_next_heap ?h p ?q) p ?c) ?c) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val ?h ?c)"
    apply (simp only:
        scheduler_next_field_update_to_whole[OF p_guard]
        scheduler_previous_field_update_to_whole[OF p_guard])
    by (rule scheduler_fresh_two_item_updates_preserve_cycle_next[
          OF rel fresh rc_cycle])
  have prefix_next:
    "Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
       (h_val
         (scheduler_insert_previous_heap
           (scheduler_insert_next_heap ?h p ?q) p ?c) ?c) = ?q"
    using prefix_unchanged next_eq by simp
  have concrete:
    "scheduler_insert_end_general_heap ?h lp xs p =
     raw_insert_concrete_heap ?h (abi_list_ptr lp) xs (abi_item_ptr p)"
    by (rule scheduler_insert_end_general_heap_abi[OF p_guard lp_guard])
  show ?thesis
    unfolding Scheduler_V611_Delay_Translation.vListInsertEnd'_def
    apply runs_to_vcg
    apply (simp_all only: hrs_mem_update)
    apply ((rule
        scheduler_insert_end_successor_guard_after_item_updates[OF rel fresh]
      | rule p_guard
      | rule lp_guard
      | rule c_guard
      | rule q_guard)+)
    apply (simp_all only: index next_eq)
    apply (simp_all add: h_val_heap_update p_guard lp_guard c_guard q_guard)
    apply (simp_all only:
        scheduler_next_state_update_to_whole[OF p_guard]
        scheduler_previous_state_update_to_whole[OF p_guard]
        scheduler_previous_state_update_to_whole[OF q_guard]
        scheduler_next_state_update_to_whole[OF c_guard]
        scheduler_insert_index_state_update_to_whole
        scheduler_container_state_update_to_whole
        scheduler_count_state_update_to_whole)
    apply (simp_all only: concrete[symmetric])
    apply (all \<open>cases s\<close>)
    apply (all \<open>simp add:
        scheduler_mem_state_def
        hrs_mem_update_def
        hrs_mem_def
        scheduler_insert_end_general_heap_def
        concrete Let_def
        split: prod.splits\<close>)
    apply (all \<open>insert index prefix_unchanged q_guard next_eq\<close>)
    apply (all \<open>clarsimp simp: hrs_mem_def\<close>)
    apply (simp_all only:
        scheduler_next_field_update_to_whole[OF p_guard, symmetric])
    apply (simp_all only: read_after_next[symmetric])
    apply (simp_all only: index_after_next index)
    apply (simp_all only:
        scheduler_previous_field_update_to_whole[OF p_guard, symmetric])
    apply (fold scheduler_insert_next_heap_def
        scheduler_insert_previous_heap_def)
    apply (simp_all only: prefix_unchanged)
    done
qed

text \<open>
  The following postcondition is intentionally capacity-free.  It records the
  word-level count increment, topology, cursor, new-item ownership, and old
  payload frame through raw_insert_effect, but does not claim that a wrapped
  machine count is equal to the mathematical length of the enlarged ring.
  The exact external frame is the union of precisely seven source fields.
\<close>

corollary scheduler_vListInsertEnd_general_capacity_free_effect:
  fixes s :: Scheduler_V611_Parse.globals
    and lp :: "Scheduler_V611_Parse.xLIST_C ptr"
    and p :: "Scheduler_V611_Parse.xLIST_ITEM_C ptr"
  assumes rel:
      "raw_xlist_rel
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
        (abi_list_ptr lp) xs"
    and fresh:
      "raw_fresh_for_insert (abi_list_ptr lp) (ring xs)
        (abi_item_ptr p)"
  shows
    "Scheduler_V611_Delay_Translation.vListInsertEnd' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       raw_insert_effect
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t))
         (abi_list_ptr lp) xs (abi_item_ptr p) \<and>
       (\<forall>a.
          a \<notin> raw_insert_end_exact_write_footprint
            (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
            (abi_list_ptr lp) xs (abi_item_ptr p)
          \<longrightarrow>
          hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t) a =
          hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s) a)
     \<rbrace>"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)"
  let ?h' =
    "raw_insert_concrete_heap ?h (abi_list_ptr lp) xs (abi_item_ptr p)"
  note exact = scheduler_vListInsertEnd_general_exact_state[OF rel fresh]
  have effect:
    "raw_insert_effect ?h ?h' (abi_list_ptr lp) xs (abi_item_ptr p)"
    by (rule raw_insert_concrete_heap_effect[OF rel fresh])
  have frame:
    "\<forall>a.
       a \<notin> raw_insert_end_exact_write_footprint
         ?h (abi_list_ptr lp) xs (abi_item_ptr p)
       \<longrightarrow> ?h' a = ?h a"
    by (intro allI impI;
        rule raw_insert_concrete_heap_exact_external_frame[OF rel fresh])
  show ?thesis
    apply (rule runs_to_weaken[OF exact])
    using effect frame by auto
qed

text \<open>
  Quantifier ledger: s, lp, p, xs, every ring element, every key, the cursor,
  and both insertion endpoints are symbolic.  There is no priority constant,
  ring non-emptiness premise, endpoint-distinctness premise, post-state
  premise, or raw_count_can_increment premise.
\<close>

end
