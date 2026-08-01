theory Scheduler_P2_Insert_Transform
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Remove_Wake_Frame.Scheduler_P2_Remove_Wake_Frame"
begin

text \<open>
  A field-precise scheduler-universe transformer for the non-maximal-key,
  empty-list path through vListInsert.  The six writes deliberately retain
  source order; the theorem below identifies every stage with the existing
  raw-byte transformer without executing the raw translation unit.
\<close>

definition scheduler_end_item ::
  "Scheduler_V611_Parse.xLIST_C ptr \<Rightarrow>
   Scheduler_V611_Parse.xLIST_ITEM_C ptr"
where
  "scheduler_end_item lp =
     PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
       &(lp\<rightarrow>[''xListEnd_C''])"

lemma scheduler_end_item_abi [simp]:
  "abi_item_ptr (scheduler_end_item lp) =
   raw_end_item (abi_list_ptr lp)"
  by (simp add: scheduler_end_item_def raw_end_item_def
      raw_sentinel_ptr_def abi_sentinel_field_address_commutes)

lemma scheduler_container_list_cast:
  "PTR_COERCE(Scheduler_V611_Parse.xLIST_C \<rightarrow> unit) lp =
   PTR_COERCE(List_V611_Raw_Skip_Translation.xLIST_C \<rightarrow> unit)
     (abi_list_ptr lp)"
  by (simp add: abi_list_ptr_def)

definition scheduler_insert_next_heap ::
  "heap_mem \<Rightarrow> Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow>
   Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow> heap_mem"
where
  "scheduler_insert_next_heap h u v =
     heap_update
       (PTR(Scheduler_V611_Parse.xLIST_ITEM_C ptr)
         &(u\<rightarrow>[''pxNext_C''])) v h"

definition scheduler_insert_previous_heap ::
  "heap_mem \<Rightarrow> Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow>
   Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow> heap_mem"
where
  "scheduler_insert_previous_heap h u v =
     heap_update
       (PTR(Scheduler_V611_Parse.xLIST_ITEM_C ptr)
         &(u\<rightarrow>[''pxPrevious_C''])) v h"

definition scheduler_insert_container_heap ::
  "heap_mem \<Rightarrow> Scheduler_V611_Parse.xLIST_C ptr \<Rightarrow>
   Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow> heap_mem"
where
  "scheduler_insert_container_heap h lp p =
     heap_update p
       (Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C_update
         (\<lambda>_. PTR_COERCE(Scheduler_V611_Parse.xLIST_C \<rightarrow> unit) lp)
         (h_val h p)) h"

definition scheduler_insert_count_heap ::
  "heap_mem \<Rightarrow> Scheduler_V611_Parse.xLIST_C ptr \<Rightarrow> heap_mem"
where
  "scheduler_insert_count_heap h lp =
     heap_update lp
       (Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C_update
         (\<lambda>n. n + 1) (h_val h lp)) h"

definition scheduler_ordered_insert_empty_heap ::
  "heap_mem \<Rightarrow> Scheduler_V611_Parse.xLIST_C ptr \<Rightarrow>
   Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow> heap_mem"
where
  "scheduler_ordered_insert_empty_heap h lp p =
     (let e = scheduler_end_item lp;
          h1 = scheduler_insert_next_heap h p e;
          h2 = scheduler_insert_previous_heap h1 e p;
          h3 = scheduler_insert_previous_heap h2 p e;
          h4 = scheduler_insert_next_heap h3 e p;
          h5 = scheduler_insert_container_heap h4 lp p
      in scheduler_insert_count_heap h5 lp)"

lemma scheduler_insert_next_heap_abi:
  "scheduler_insert_next_heap h u v =
   raw_insert_next_heap h (abi_item_ptr u) (abi_item_ptr v)"
  unfolding scheduler_insert_next_heap_def raw_insert_next_heap_def
    raw_next_field_ptr_def
  by (rule abi_item_next_field_write)

lemma scheduler_insert_previous_heap_abi:
  "scheduler_insert_previous_heap h u v =
   raw_insert_previous_heap h (abi_item_ptr u) (abi_item_ptr v)"
  unfolding scheduler_insert_previous_heap_def raw_insert_previous_heap_def
    raw_previous_field_ptr_def
  by (rule abi_item_previous_field_write)

lemma scheduler_insert_container_heap_abi:
  assumes guard: "c_guard p"
  shows
    "scheduler_insert_container_heap h lp p =
     raw_insert_container_heap h (abi_list_ptr lp) (abi_item_ptr p)"
  unfolding scheduler_insert_container_heap_def raw_insert_container_heap_def
  apply (simp only: scheduler_container_list_cast)
  apply (rule abi_item_container_whole_write[OF guard])
  done

lemma scheduler_insert_count_heap_abi:
  assumes guard: "c_guard lp"
  shows
    "scheduler_insert_count_heap h lp =
     raw_insert_count_heap h (abi_list_ptr lp)"
  unfolding scheduler_insert_count_heap_def raw_insert_count_heap_def
  apply (subst scheduler_list_count_update_to_constant)
  apply (subst raw_list_count_update_to_constant)
  apply (simp only: abi_list_count_h_val)
  apply (rule abi_list_count_whole_write[OF guard])
  done

lemma scheduler_ordered_insert_empty_heap_abi:
  assumes item_guard: "c_guard p"
    and list_guard: "c_guard lp"
  shows
    "scheduler_ordered_insert_empty_heap h lp p =
     raw_ordered_insert_empty_heap h (abi_list_ptr lp) (abi_item_ptr p)"
  unfolding scheduler_ordered_insert_empty_heap_def
    raw_ordered_insert_empty_heap_def Let_def
  by (simp only: scheduler_end_item_abi
      scheduler_insert_next_heap_abi scheduler_insert_previous_heap_abi
      scheduler_insert_container_heap_abi[OF item_guard]
      scheduler_insert_count_heap_abi[OF list_guard])

end
