theory Scheduler_P2_Remove_Source
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Source_Footprint.Scheduler_P2_Source_Footprint"
begin

text \<open>
  Scheduler-translation-unit normalisation for vListRemove starts below the
  generated monad body.  Each lemma equates one scheduler-universe byte-heap
  update with its raw-list counterpart; the two generated record types remain
  distinct throughout.
\<close>

lemma abi_container_list_cast:
  "abi_list_ptr
      (PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.xLIST_C) c) =
   PTR_COERCE(unit \<rightarrow>
      List_V611_Raw_Skip_Translation.xLIST_C) c"
  by (simp add: abi_list_ptr_def)

lemma abi_list_index_whole_write:
  assumes guard: "c_guard lp"
  shows
    "heap_update lp
       (Scheduler_V611_Parse.xLIST_C.pxIndex_C_update (\<lambda>_. q)
         (h_val h lp)) h =
     heap_update (abi_list_ptr lp)
       (List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C_update
         (\<lambda>_. abi_item_ptr q)
         (h_val h (abi_list_ptr lp))) h"
proof -
  have raw_guard: "c_guard (abi_list_ptr lp)"
    using guard by (rule iffD2[OF abi_list_ptr_c_guard])
  have scheduler_field:
    "heap_update lp
       (Scheduler_V611_Parse.xLIST_C.pxIndex_C_update (\<lambda>_. q)
         (h_val h lp)) h =
     heap_update
       (PTR(Scheduler_V611_Parse.xLIST_ITEM_C ptr)
         &(lp\<rightarrow>[''pxIndex_C''])) q h"
    by (rule sym;
        rule Scheduler_V611_Parse.xLIST_C_heap_update_fields(2)[OF guard])
  have raw_field:
    "heap_update
       (PTR(List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr)
         &((abi_list_ptr lp)\<rightarrow>[''pxIndex_C'']))
       (abi_item_ptr q) h =
     heap_update (abi_list_ptr lp)
       (List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C_update
         (\<lambda>_. abi_item_ptr q)
         (h_val h (abi_list_ptr lp))) h"
    by (rule
      List_V611_Raw_Skip_Translation.xLIST_C_heap_update_fields(2)[
        OF raw_guard])
  show ?thesis
    using scheduler_field abi_list_index_field_write[where h=h]
      raw_field by simp
qed

lemma abi_item_container_whole_write:
  assumes guard: "c_guard p"
  shows
    "heap_update p
       (Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C_update (\<lambda>_. c)
         (h_val h p)) h =
     heap_update (abi_item_ptr p)
       (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C_update
         (\<lambda>_. c) (h_val h (abi_item_ptr p))) h"
proof -
  have raw_guard: "c_guard (abi_item_ptr p)"
    using guard by (rule iffD2[OF abi_item_ptr_c_guard])
  have scheduler_field:
    "heap_update p
       (Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C_update (\<lambda>_. c)
         (h_val h p)) h =
     heap_update
       (PTR(unit ptr) &(p\<rightarrow>[''pvContainer_C''])) c h"
    by (rule sym;
        rule Scheduler_V611_Parse.xLIST_ITEM_C_heap_update_fields(5)[
          OF guard])
  have raw_field:
    "heap_update
       (PTR(unit ptr)
         &((abi_item_ptr p)\<rightarrow>[''pvContainer_C''])) c h =
     heap_update (abi_item_ptr p)
       (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C_update
         (\<lambda>_. c) (h_val h (abi_item_ptr p))) h"
    by (rule
      List_V611_Raw_Skip_Translation.xLIST_ITEM_C_heap_update_fields(5)[
        OF raw_guard])
  show ?thesis
    using scheduler_field abi_item_container_field_write[where h=h]
      raw_field by simp
qed

lemma abi_list_count_whole_write:
  assumes guard: "c_guard lp"
  shows
    "heap_update lp
       (Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C_update (\<lambda>_. n)
         (h_val h lp)) h =
     heap_update (abi_list_ptr lp)
       (List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C_update
         (\<lambda>_. n) (h_val h (abi_list_ptr lp))) h"
proof -
  have raw_guard: "c_guard (abi_list_ptr lp)"
    using guard by (rule iffD2[OF abi_list_ptr_c_guard])
  have scheduler_field:
    "heap_update lp
       (Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C_update (\<lambda>_. n)
         (h_val h lp)) h =
     heap_update
       (PTR(32 word) &(lp\<rightarrow>[''uxNumberOfItems_C''])) n h"
    by (rule sym;
        rule Scheduler_V611_Parse.xLIST_C_heap_update_fields(1)[OF guard])
  have raw_field:
    "heap_update
       (PTR(32 word)
         &((abi_list_ptr lp)\<rightarrow>[''uxNumberOfItems_C''])) n h =
     heap_update (abi_list_ptr lp)
       (List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C_update
         (\<lambda>_. n) (h_val h (abi_list_ptr lp))) h"
    by (rule
      List_V611_Raw_Skip_Translation.xLIST_C_heap_update_fields(1)[
        OF raw_guard])
  show ?thesis
    using scheduler_field abi_list_count_field_write[where h=h]
      raw_field by simp
qed

lemma scheduler_list_count_update_to_constant:
  "Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C_update f x =
   Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C_update
     (\<lambda>_. f (Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C x)) x"
  by (cases x) simp

lemma raw_list_count_update_to_constant:
  "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C_update f x =
   List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C_update
     (\<lambda>_. f
       (List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C x)) x"
  by (cases x) simp

definition scheduler_source_unlink_first ::
  "heap_mem \<Rightarrow> Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow>
   heap_mem"
where
  "scheduler_source_unlink_first h p =
     heap_update
       (PTR(Scheduler_V611_Parse.xLIST_ITEM_C ptr)
         &((Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h p))
           \<rightarrow>[''pxPrevious_C'']))
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxPrevious_C (h_val h p)) h"

lemma scheduler_source_unlink_first_abi:
  "scheduler_source_unlink_first h p =
   raw_source_unlink_first h (abi_item_ptr p)"
  unfolding scheduler_source_unlink_first_def raw_source_unlink_first_def
    raw_previous_field_ptr_def
  apply (simp only: abi_item_next_h_val abi_item_previous_h_val)
  apply (rule abi_item_previous_field_write)
  done

definition scheduler_source_unlink_two ::
  "heap_mem \<Rightarrow> Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow>
   heap_mem"
where
  "scheduler_source_unlink_two h p =
     (let h1 = scheduler_source_unlink_first h p
      in heap_update
        (PTR(Scheduler_V611_Parse.xLIST_ITEM_C ptr)
          &((Scheduler_V611_Parse.xLIST_ITEM_C.pxPrevious_C
             (h_val h1 p))\<rightarrow>[''pxNext_C'']))
        (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h1 p)) h1)"

lemma scheduler_source_unlink_two_abi:
  "scheduler_source_unlink_two h p =
   raw_source_unlink_two h (abi_item_ptr p)"
  unfolding scheduler_source_unlink_two_def raw_source_unlink_two_def
    raw_next_field_ptr_def Let_def
  apply (simp only: scheduler_source_unlink_first_abi
      abi_item_previous_h_val abi_item_next_h_val)
  apply (rule abi_item_next_field_write)
  done

definition scheduler_remove_index_heap ::
  "heap_mem \<Rightarrow> Scheduler_V611_Parse.xLIST_C ptr \<Rightarrow>
   Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow> heap_mem"
where
  "scheduler_remove_index_heap h lp p =
     (if Scheduler_V611_Parse.xLIST_C.pxIndex_C (h_val h lp) = p
      then heap_update lp
        (Scheduler_V611_Parse.xLIST_C.pxIndex_C_update
          (\<lambda>_. Scheduler_V611_Parse.xLIST_ITEM_C.pxPrevious_C
            (h_val h p))
          (h_val h lp)) h
      else h)"

lemma scheduler_remove_index_heap_abi:
  assumes guard: "c_guard lp"
  shows
    "scheduler_remove_index_heap h lp p =
     raw_remove_index_heap h (abi_list_ptr lp) (abi_item_ptr p)"
  unfolding scheduler_remove_index_heap_def raw_remove_index_heap_def
  by (simp add: abi_list_index_h_val abi_item_previous_h_val
      abi_list_index_whole_write[OF guard])

definition scheduler_remove_container_heap ::
  "heap_mem \<Rightarrow> Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow>
   heap_mem"
where
  "scheduler_remove_container_heap h p =
     heap_update p
       (Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C_update
         (\<lambda>_. NULL) (h_val h p)) h"

lemma scheduler_remove_container_heap_abi:
  assumes guard: "c_guard p"
  shows
    "scheduler_remove_container_heap h p =
     raw_remove_container_heap h (abi_item_ptr p)"
  unfolding scheduler_remove_container_heap_def
    raw_remove_container_heap_def
  by (rule abi_item_container_whole_write[OF guard])

definition scheduler_remove_count_heap ::
  "heap_mem \<Rightarrow> Scheduler_V611_Parse.xLIST_C ptr \<Rightarrow>
   heap_mem"
where
  "scheduler_remove_count_heap h lp =
     heap_update lp
       (Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C_update
         (\<lambda>n. n - 1) (h_val h lp)) h"

lemma scheduler_remove_count_heap_abi:
  assumes guard: "c_guard lp"
  shows
    "scheduler_remove_count_heap h lp =
     raw_remove_count_heap h (abi_list_ptr lp)"
  unfolding scheduler_remove_count_heap_def raw_remove_count_heap_def
  apply (subst scheduler_list_count_update_to_constant)
  apply (subst raw_list_count_update_to_constant)
  apply (simp only: abi_list_count_h_val)
  apply (rule abi_list_count_whole_write[OF guard])
  done

definition scheduler_remove_suffix_heap ::
  "heap_mem \<Rightarrow> Scheduler_V611_Parse.xLIST_C ptr \<Rightarrow>
   Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow> heap_mem"
where
  "scheduler_remove_suffix_heap h lp p =
     scheduler_remove_count_heap
       (scheduler_remove_container_heap
         (scheduler_remove_index_heap h lp p) p) lp"

lemma scheduler_remove_suffix_heap_abi:
  assumes list_guard: "c_guard lp"
    and item_guard: "c_guard p"
  shows
    "scheduler_remove_suffix_heap h lp p =
     raw_remove_suffix_heap h (abi_list_ptr lp) (abi_item_ptr p)"
  unfolding scheduler_remove_suffix_heap_def raw_remove_suffix_heap_def
  by (simp only:
      scheduler_remove_index_heap_abi[OF list_guard]
      scheduler_remove_container_heap_abi[OF item_guard]
      scheduler_remove_count_heap_abi[OF list_guard])

definition scheduler_remove_concrete_heap ::
  "heap_mem \<Rightarrow> Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow>
   heap_mem"
where
  "scheduler_remove_concrete_heap h p =
     (let hu = scheduler_source_unlink_two h p;
          lp = PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.xLIST_C)
            (Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C
              (h_val hu p))
      in scheduler_remove_suffix_heap hu lp p)"

lemma scheduler_remove_concrete_heap_abi:
  assumes item_guard: "c_guard p"
    and list_guard:
      "c_guard
        (PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.xLIST_C)
          (Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C
            (h_val (scheduler_source_unlink_two h p) p)))"
  shows
    "scheduler_remove_concrete_heap h p =
     raw_remove_concrete_heap h (abi_item_ptr p)"
proof -
  let ?shu = "scheduler_source_unlink_two h p"
  let ?rhu = "raw_source_unlink_two h (abi_item_ptr p)"
  let ?slp =
    "PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.xLIST_C)
      (Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C (h_val ?shu p))"
  let ?rlp =
    "PTR_COERCE(unit \<rightarrow>
       List_V611_Raw_Skip_Translation.xLIST_C)
      (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
        (h_val ?rhu (abi_item_ptr p)))"
  have unlink: "?shu = ?rhu"
    by (rule scheduler_source_unlink_two_abi)
  have list_ptr: "abi_list_ptr ?slp = ?rlp"
    using unlink
    by (simp add: abi_item_container_h_val abi_container_list_cast)
  have suffix:
    "scheduler_remove_suffix_heap ?shu ?slp p =
     raw_remove_suffix_heap ?shu (abi_list_ptr ?slp) (abi_item_ptr p)"
    by (rule scheduler_remove_suffix_heap_abi[
          OF list_guard item_guard])
  show ?thesis
    using unlink list_ptr suffix
    by (simp add: scheduler_remove_concrete_heap_def
        raw_remove_concrete_heap_def Let_def)
qed

lemma scheduler_remove_dynamic_guards:
  assumes rel:
      "raw_xlist_rel h (abi_list_ptr lp) xs"
    and member: "abi_item_ptr p \<in> set (ring xs)"
  shows
    "c_guard p \<and>
     c_guard
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h p)) \<and>
     c_guard
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxPrevious_C (h_val h p)) \<and>
     c_guard
       (PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.xLIST_C)
         (Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C (h_val h p)))"
proof -
  note raw_guards = raw_vListRemove_dynamic_guards[OF rel member]
  have raw_item: "c_guard (abi_item_ptr p)"
    using raw_guards by blast
  have item: "c_guard p"
    using raw_item by (rule iffD1[OF abi_item_ptr_c_guard])
  have raw_next:
    "c_guard
      (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxNext_C
        (h_val h (abi_item_ptr p)))"
    using raw_guards by blast
  have coerced_next:
    "c_guard
      (abi_item_ptr
        (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h p)))"
    using raw_next by (simp only: abi_item_next_h_val)
  have next_guard:
    "c_guard
      (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h p))"
    using coerced_next by (rule iffD1[OF abi_item_ptr_c_guard])
  have raw_previous:
    "c_guard
      (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxPrevious_C
        (h_val h (abi_item_ptr p)))"
    using raw_guards by blast
  have coerced_previous:
    "c_guard
      (abi_item_ptr
        (Scheduler_V611_Parse.xLIST_ITEM_C.pxPrevious_C (h_val h p)))"
    using raw_previous by (simp only: abi_item_previous_h_val)
  have previous_guard:
    "c_guard
      (Scheduler_V611_Parse.xLIST_ITEM_C.pxPrevious_C (h_val h p))"
    using coerced_previous by (rule iffD1[OF abi_item_ptr_c_guard])
  let ?slp =
    "PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.xLIST_C)
      (Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C (h_val h p))"
  have raw_container:
    "c_guard
      (PTR_COERCE(unit \<rightarrow>
         List_V611_Raw_Skip_Translation.xLIST_C)
        (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
          (h_val h (abi_item_ptr p))))"
    using raw_guards by blast
  have coerced_container: "c_guard (abi_list_ptr ?slp)"
    using raw_container
    by (simp only: abi_item_container_h_val abi_container_list_cast)
  have container: "c_guard ?slp"
    using coerced_container by (rule iffD1[OF abi_list_ptr_c_guard])
  show ?thesis
    using item next_guard previous_guard container by blast
qed

lemma scheduler_remove_previous_guard_after_first_unlink:
  assumes rel:
      "raw_xlist_rel h (abi_list_ptr lp) xs"
    and member: "abi_item_ptr p \<in> set (ring xs)"
  shows
    "c_guard
      (Scheduler_V611_Parse.xLIST_ITEM_C.pxPrevious_C
        (h_val (scheduler_source_unlink_first h p) p))"
proof -
  have initial:
    "c_guard
      (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxPrevious_C
        (h_val h (abi_item_ptr p)))"
    using raw_vListRemove_dynamic_guards[OF rel member] by blast
  have stable:
    "h_val (raw_source_unlink_first h (abi_item_ptr p))
       (abi_item_ptr p) =
     h_val h (abi_item_ptr p)"
    unfolding raw_source_unlink_first_def
    by (rule raw_remove_first_unlink_preserves_item[OF rel member])
  have after_raw:
    "c_guard
      (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxPrevious_C
        (h_val (scheduler_source_unlink_first h p) (abi_item_ptr p)))"
    using initial stable scheduler_source_unlink_first_abi by simp
  have coerced:
    "c_guard
      (abi_item_ptr
        (Scheduler_V611_Parse.xLIST_ITEM_C.pxPrevious_C
          (h_val (scheduler_source_unlink_first h p) p)))"
    using after_raw by (simp only: abi_item_previous_h_val)
  show ?thesis
    using coerced by (rule iffD1[OF abi_item_ptr_c_guard])
qed

lemma scheduler_remove_container_guard_after_two_unlinks:
  assumes rel:
      "raw_xlist_rel h (abi_list_ptr lp) xs"
    and member: "abi_item_ptr p \<in> set (ring xs)"
  shows
    "c_guard
      (PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.xLIST_C)
        (Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C
          (h_val (scheduler_source_unlink_two h p) p)))"
proof -
  have initial:
    "c_guard
      (PTR_COERCE(unit \<rightarrow>
         List_V611_Raw_Skip_Translation.xLIST_C)
        (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
          (h_val h (abi_item_ptr p))))"
    using raw_vListRemove_dynamic_guards[OF rel member] by blast
  have stable:
    "h_val (raw_source_unlink_two h (abi_item_ptr p))
       (abi_item_ptr p) =
     h_val h (abi_item_ptr p)"
    by (rule raw_source_unlink_two_item_same[OF rel member])
  let ?slp =
    "PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.xLIST_C)
      (Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C
        (h_val (scheduler_source_unlink_two h p) p))"
  have after_raw:
    "c_guard
      (PTR_COERCE(unit \<rightarrow>
         List_V611_Raw_Skip_Translation.xLIST_C)
        (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
          (h_val (scheduler_source_unlink_two h p) (abi_item_ptr p))))"
    using initial stable scheduler_source_unlink_two_abi by simp
  have coerced: "c_guard (abi_list_ptr ?slp)"
    using after_raw
    by (simp only: abi_item_container_h_val abi_container_list_cast)
  show ?thesis
    using coerced by (rule iffD1[OF abi_list_ptr_c_guard])
qed

definition scheduler_mem_state ::
  "heap_mem \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   Scheduler_V611_Parse.globals"
where
  "scheduler_mem_state h c =
     Scheduler_V611_Parse.globals.t_hrs_'_update
       (hrs_mem_update (\<lambda>_. h)) c"

lemma scheduler_heap_modify_as_mem_state:
  "Scheduler_V611_Parse.globals.t_hrs_'_update
      (hrs_mem_update f) c =
   scheduler_mem_state
     (f (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))) c"
  by (cases c)
     (simp add: scheduler_mem_state_def hrs_mem_update_def hrs_mem_def
        split: prod.splits)

lemma scheduler_mem_state_comp [simp]:
  "scheduler_mem_state h' (scheduler_mem_state h c) =
   scheduler_mem_state h' c"
  by (cases c)
     (simp add: scheduler_mem_state_def hrs_mem_update_def hrs_mem_def
        split: prod.splits)

lemma scheduler_t_hrs_update_comp:
  "Scheduler_V611_Parse.globals.t_hrs_'_update (f \<circ> g) c =
   Scheduler_V611_Parse.globals.t_hrs_'_update f
     (Scheduler_V611_Parse.globals.t_hrs_'_update g c)"
  by (cases c) simp

lemma scheduler_heap_transform_as_mem_state:
  "Scheduler_V611_Parse.globals.t_hrs_'_update
      (\<lambda>hrs. hrs_mem_update (f (hrs_mem hrs)) hrs) c =
   scheduler_mem_state
     ((f (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))) c"
  by (cases c)
     (simp add: scheduler_mem_state_def hrs_mem_update_def hrs_mem_def
        split: prod.splits)

lemma scheduler_mem_state_heap [simp]:
  "hrs_mem
      (Scheduler_V611_Parse.globals.t_hrs_'
        (scheduler_mem_state h c)) = h"
  by (cases c)
     (simp add: scheduler_mem_state_def hrs_mem_update_def hrs_mem_def
        split: prod.splits)

lemma scheduler_mem_state_eq_iff [simp]:
  "scheduler_mem_state h c = scheduler_mem_state h' c \<longleftrightarrow> h = h'"
  by (cases c)
     (simp add: scheduler_mem_state_def hrs_mem_update_def hrs_mem_def
        split: prod.splits)

theorem scheduler_vListRemove_p2_ready2_exact_state:
  fixes s :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R s p2_pre"
  shows
    "Scheduler_V611_Delay_Translation.vListRemove'
       (scheduler_generic_item_ptr (sd_tcb_ptr D P2_RUN)) \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_mem_state
         (raw_remove_concrete_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
           (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))) s
     \<rbrace>"
proof -
  let ?sp =
    "scheduler_generic_item_ptr (sd_tcb_ptr D P2_RUN)"
  let ?rp = "abi_item_ptr ?sp"
  let ?h =
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)"
  from p2_pre_ready2_raw_singletonE[OF decode lists]
  obtain rx where
      rel:
        "raw_xlist_rel ?h (abi_list_ptr (sr_ready R 2)) rx"
    and ring:
        "ring rx =
          [abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)]"
    and cursor:
        "cursor rx =
          Some (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))" .
  have member: "?rp \<in> set (ring rx)"
    using ring by simp
  note guards = scheduler_remove_dynamic_guards[OF rel member]
  have item_guard: "c_guard ?sp"
    using guards by blast
  have next_guard:
    "c_guard
      (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val ?h ?sp))"
    using guards by blast
  have previous_guard:
    "c_guard
      (Scheduler_V611_Parse.xLIST_ITEM_C.pxPrevious_C
        (h_val (scheduler_source_unlink_first ?h ?sp) ?sp))"
    by (rule scheduler_remove_previous_guard_after_first_unlink[
          OF rel member])
  have container_guard:
    "c_guard
      (PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.xLIST_C)
        (Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C
          (h_val (scheduler_source_unlink_two ?h ?sp) ?sp)))"
    by (rule scheduler_remove_container_guard_after_two_unlinks[
          OF rel member])
  note container_guard_expanded =
    container_guard[unfolded scheduler_source_unlink_two_def Let_def]
  have concrete:
    "raw_remove_concrete_heap ?h
       (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)) =
     scheduler_remove_concrete_heap ?h ?sp"
    using scheduler_remove_concrete_heap_abi[
      OF item_guard container_guard]
    by simp
  show ?thesis
    unfolding Scheduler_V611_Delay_Translation.vListRemove'_def
    apply runs_to_vcg
    apply (simp_all only: hrs_mem_update)
    apply (fold scheduler_source_unlink_first_def)
    apply ((rule
        previous_guard
      | rule container_guard_expanded
      | rule item_guard
      | rule next_guard)+)
    apply (simp_all only: concrete)
    apply (all \<open>cases s\<close>)
    apply (all \<open>simp add:
        scheduler_mem_state_def
        hrs_mem_update_def
        hrs_mem_def
        scheduler_remove_concrete_heap_def
        scheduler_source_unlink_two_def
        scheduler_source_unlink_first_def
        scheduler_remove_suffix_heap_def
        scheduler_remove_index_heap_def
        scheduler_remove_container_heap_def
        scheduler_remove_count_heap_def
        concrete Let_def
        split: prod.splits\<close>)
    done
qed

corollary scheduler_vListRemove_p2_ready2_normal_form:
  fixes s :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R s p2_pre"
  shows
    "Scheduler_V611_Delay_Translation.vListRemove'
       (scheduler_generic_item_ptr (sd_tcb_ptr D P2_RUN)) \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t) =
         raw_remove_concrete_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
           (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))
     \<rbrace>"
proof -
  note exact = scheduler_vListRemove_p2_ready2_exact_state[
      OF decode lists]
  show ?thesis
    apply (rule runs_to_weaken[OF exact])
    by (auto simp: scheduler_mem_state_def hrs_mem_update)
qed

end
