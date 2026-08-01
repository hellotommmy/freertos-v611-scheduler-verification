theory Scheduler_P2_Insert_Source
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Insert_Frame.Scheduler_P2_Insert_Frame"
begin

text \<open>
  Source normalisation for the scheduler translation unit's ordered insertion
  routine.  This proof opens the scheduler body exactly once and discharges
  its non-maximal-key, empty-list path.  It does not invoke the independently
  translated raw-list monadic theorem.
\<close>

lemma scheduler_next_field_update_to_whole:
  assumes guard: "c_guard u"
  shows
    "scheduler_insert_next_heap h u q =
     heap_update u
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C_update
         (\<lambda>_. q) (h_val h u)) h"
  unfolding scheduler_insert_next_heap_def
  by (rule Scheduler_V611_Parse.xLIST_ITEM_C_heap_update_fields(2)[
        OF guard])

lemma scheduler_previous_field_update_to_whole:
  assumes guard: "c_guard u"
  shows
    "scheduler_insert_previous_heap h u q =
     heap_update u
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxPrevious_C_update
         (\<lambda>_. q) (h_val h u)) h"
  unfolding scheduler_insert_previous_heap_def
  by (rule Scheduler_V611_Parse.xLIST_ITEM_C_heap_update_fields(3)[
        OF guard])

lemma scheduler_ordered_empty_source_next:
  assumes rel: "raw_xlist_rel h (abi_list_ptr lp) xs"
    and empty: "ring xs = []"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
       (h_val h (scheduler_end_item lp)) = scheduler_end_item lp"
  using raw_ordered_empty_source_next[OF rel empty]
  by (simp only: scheduler_end_item_abi[symmetric]
      abi_item_next_h_val abi_item_ptr_eq_iff)

lemma scheduler_ordered_empty_source_loop_guard_false:
  assumes rel: "raw_xlist_rel h (abi_list_ptr lp) xs"
    and empty: "ring xs = []"
    and sentinel: "raw_sentinel_max h (abi_list_ptr lp)"
    and nonmax:
      "raw_key_at h (abi_item_ptr p) \<noteq> (max_word :: 32 word)"
  shows
    "\<not>
      (Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
         (h_val h
           (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
             (h_val h (scheduler_end_item lp))))
       \<le> Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val h p))"
proof -
  let ?e = "scheduler_end_item lp"
  have raw_false:
    "\<not>
      (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.xItemValue_C
         (h_val h
           (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxNext_C
             (h_val h (raw_end_item (abi_list_ptr lp)))))
       \<le> List_V611_Raw_Skip_Translation.xLIST_ITEM_C.xItemValue_C
         (h_val h (abi_item_ptr p)))"
    by (rule raw_ordered_empty_source_loop_guard_false[OF
          rel empty sentinel nonmax])
  have next_ptr:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxNext_C
       (h_val h (raw_end_item (abi_list_ptr lp))) =
     abi_item_ptr
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h ?e))"
    using abi_item_next_h_val[where h=h and p="?e"] by simp
  have next_key:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.xItemValue_C
       (h_val h
         (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxNext_C
           (h_val h (raw_end_item (abi_list_ptr lp))))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (h_val h
         (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h ?e)))"
    using abi_item_key_h_val[
        where h=h and
          p="Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h ?e)"]
      next_ptr by simp
  have item_key:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.xItemValue_C
       (h_val h (abi_item_ptr p)) =
     Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val h p)"
    by (rule abi_item_key_h_val)
  show ?thesis using raw_false next_key item_key by simp
qed

theorem scheduler_vListInsert_ordered_empty_nonmax_exact_state:
  fixes s :: Scheduler_V611_Parse.globals
  assumes rel:
      "raw_xlist_rel
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
        (abi_list_ptr lp) xs"
    and empty: "ring xs = []"
    and fresh:
      "raw_fresh_for_insert (abi_list_ptr lp) (ring xs)
        (abi_item_ptr p)"
    and sentinel:
      "raw_sentinel_max
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
        (abi_list_ptr lp)"
    and key_nonmax:
      "raw_key_at
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
        (abi_item_ptr p) \<noteq> (max_word :: 32 word)"
  shows
    "Scheduler_V611_Delay_Translation.vListInsert' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_mem_state
         (raw_ordered_insert_empty_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
           (abi_list_ptr lp) (abi_item_ptr p)) s
     \<rbrace>"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)"
  let ?e = "scheduler_end_item lp"
  have raw_p_guard: "c_guard (abi_item_ptr p)"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have p_guard: "c_guard p"
    using raw_p_guard by (rule iffD1[OF abi_item_ptr_c_guard])
  have raw_lp_guard: "c_guard (abi_list_ptr lp)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_layout_def)
  have lp_guard: "c_guard lp"
    using raw_lp_guard by (rule iffD1[OF abi_list_ptr_c_guard])
  have raw_e_guard: "c_guard (raw_end_item (abi_list_ptr lp))"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_layout_def)
  have coerced_e_guard: "c_guard (abi_item_ptr ?e)"
    using raw_e_guard by simp
  have e_guard: "c_guard ?e"
    using coerced_e_guard by (rule iffD1[OF abi_item_ptr_c_guard])
  have hex_max:
    "(0xFFFFFFFF :: 32 word) = (max_word :: 32 word)"
    by simp
  have key_nonvalue:
    "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val ?h p)
       \<noteq> 0xFFFFFFFF"
    apply (subst hex_max)
    using key_nonmax
    by (simp add: raw_key_at_def abi_item_key_h_val)
  have sentinel_ptr:
    "PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
       &(lp\<rightarrow>[''xListEnd_C'']) = ?e"
    by (simp add: scheduler_end_item_def)
  have end_next:
    "Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val ?h ?e) = ?e"
    by (rule scheduler_ordered_empty_source_next[OF rel empty])
  have loop_false:
    "\<not>
      (Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
         (h_val ?h
           (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
             (h_val ?h ?e)))
       \<le> Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
         (h_val ?h p))"
    by (rule scheduler_ordered_empty_source_loop_guard_false[OF
          rel empty sentinel key_nonmax])
  have concrete:
    "raw_ordered_insert_empty_heap ?h
       (abi_list_ptr lp) (abi_item_ptr p) =
     scheduler_ordered_insert_empty_heap ?h lp p"
    using scheduler_ordered_insert_empty_heap_abi[OF p_guard lp_guard]
    by simp
  show ?thesis
    unfolding Scheduler_V611_Delay_Translation.vListInsert'_def
    apply runs_to_vcg
    apply (simp_all only:
        hrs_mem_update key_nonvalue sentinel_ptr end_next loop_false)
    apply (simp_all add:
        h_val_heap_update p_guard lp_guard e_guard)
    apply (subst runs_to_whileLoop_cond_fail)
     apply (rule loop_false)
    apply runs_to_vcg
    apply (simp_all only: hrs_mem_update end_next)
    apply (simp_all add:
        h_val_heap_update p_guard lp_guard e_guard)
    apply (simp_all only: concrete)
    apply (all \<open>cases s\<close>)
    apply (all \<open>simp add:
        scheduler_mem_state_def
        hrs_mem_update_def
        hrs_mem_def
        split: prod.splits\<close>)
    apply (simp_all only:
        scheduler_next_field_update_to_whole[OF p_guard, symmetric]
        scheduler_previous_field_update_to_whole[OF p_guard, symmetric]
        scheduler_next_field_update_to_whole[OF e_guard, symmetric])
    apply (fold scheduler_insert_previous_heap_def)
    apply (fold scheduler_insert_container_heap_def
        scheduler_insert_count_heap_def)
    apply (all \<open>clarify\<close>)
    apply (insert end_next)
    apply (all \<open>hypsubst\<close>)
    apply (simp_all add:
        hrs_mem_def
        scheduler_ordered_insert_empty_heap_def concrete Let_def)
    done
qed

corollary scheduler_vListInsert_ordered_empty_nonmax_heap_effect:
  fixes s :: Scheduler_V611_Parse.globals
  assumes rel:
      "raw_xlist_rel
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
        (abi_list_ptr lp) xs"
    and empty: "ring xs = []"
    and fresh:
      "raw_fresh_for_insert (abi_list_ptr lp) (ring xs)
        (abi_item_ptr p)"
    and sentinel:
      "raw_sentinel_max
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
        (abi_list_ptr lp)"
    and key_nonmax:
      "raw_key_at
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
        (abi_item_ptr p) \<noteq> (max_word :: 32 word)"
  shows
    "Scheduler_V611_Delay_Translation.vListInsert' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t) =
         raw_ordered_insert_empty_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
           (abi_list_ptr lp) (abi_item_ptr p)
     \<rbrace>"
proof -
  note exact = scheduler_vListInsert_ordered_empty_nonmax_exact_state[
      OF rel empty fresh sentinel key_nonmax]
  show ?thesis
    apply (rule runs_to_weaken[OF exact])
    by (auto simp: scheduler_mem_state_def hrs_mem_update)
qed

theorem scheduler_vListInsert_p2_delayed_a_after_remove_wake_exact_state:
  fixes s0 s1 :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R s0 p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s0))"
    and heap_entry:
      "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s1) =
       p2_remove_then_wake_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s0)) D"
  shows
    "Scheduler_V611_Delay_Translation.vListInsert'
       (sr_delayed_a R)
       (scheduler_generic_item_ptr (sd_tcb_ptr D P2_RUN)) \<bullet> s1
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_mem_state
         (raw_ordered_insert_empty_heap
           (p2_remove_then_wake_heap
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s0)) D)
           (abi_list_ptr (sr_delayed_a R))
           (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))) s1
     \<rbrace>"
proof -
  let ?h0 = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s0)"
  let ?hk = "p2_remove_then_wake_heap ?h0 D"
  let ?lp = "sr_delayed_a R"
  let ?sp = "scheduler_generic_item_ptr (sd_tcb_ptr D P2_RUN)"
  let ?rp = "abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)"
  from p2_remove_then_wake_delayed_a_ordered_emptyE[
      OF decode lists footprint]
  obtain rx where
      rel: "raw_xlist_rel ?hk (abi_list_ptr ?lp) rx"
    and empty: "ring rx = []"
    and cursor: "cursor rx = None"
    and sentinel: "raw_sentinel_max ?hk (abi_list_ptr ?lp)"
    and fresh:
      "raw_fresh_for_insert (abi_list_ptr ?lp) (ring rx) ?rp"
    and key: "raw_key_at ?hk ?rp = 7" .
  have item_abi: "abi_item_ptr ?sp = ?rp"
    by simp
  have rel_entry:
    "raw_xlist_rel
      (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s1))
      (abi_list_ptr ?lp) rx"
    using rel heap_entry by simp
  have sentinel_entry:
    "raw_sentinel_max
      (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s1))
      (abi_list_ptr ?lp)"
    using sentinel heap_entry by simp
  have fresh_entry:
    "raw_fresh_for_insert (abi_list_ptr ?lp) (ring rx)
      (abi_item_ptr ?sp)"
    using fresh item_abi by simp
  have nonmax_entry:
    "raw_key_at
      (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s1))
      (abi_item_ptr ?sp) \<noteq> (max_word :: 32 word)"
    using key heap_entry item_abi by simp
  note source = scheduler_vListInsert_ordered_empty_nonmax_exact_state[
      where s=s1 and lp="?lp" and p="?sp" and xs=rx,
      OF rel_entry empty fresh_entry sentinel_entry nonmax_entry]
  show ?thesis
    using source heap_entry item_abi by simp
qed

corollary scheduler_vListInsert_p2_delayed_a_after_remove_wake:
  fixes s0 s1 :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R s0 p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s0))"
    and heap_entry:
      "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s1) =
       p2_remove_then_wake_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s0)) D"
  shows
    "Scheduler_V611_Delay_Translation.vListInsert'
       (sr_delayed_a R)
       (scheduler_generic_item_ptr (sd_tcb_ptr D P2_RUN)) \<bullet> s1
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t) =
         raw_ordered_insert_empty_heap
           (p2_remove_then_wake_heap
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s0)) D)
           (abi_list_ptr (sr_delayed_a R))
           (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))
     \<rbrace>"
proof -
  note exact =
    scheduler_vListInsert_p2_delayed_a_after_remove_wake_exact_state[
      OF decode lists footprint heap_entry]
  show ?thesis
    apply (rule runs_to_weaken[OF exact])
    by (auto simp: scheduler_mem_state_def hrs_mem_update)
qed

end
