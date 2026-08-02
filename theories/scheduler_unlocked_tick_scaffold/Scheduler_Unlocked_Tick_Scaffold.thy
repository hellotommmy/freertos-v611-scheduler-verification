theory Scheduler_Unlocked_Tick_Scaffold
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Outer_Scaffold.Scheduler_Resume_Outer_Scaffold"
    "EAL6_FreeRTOS_V611_Scheduler_Remove_Translation_General.Scheduler_Remove_Translation_General"
begin

text \<open>
  Universal source-order scaffold for the unlocked branch of
  vTaskIncrementTick.  The tick value, wrap branch, delayed-ring population,
  due prefix, event membership, priorities, roots, heap and aliases are all
  quantified.  A due prefix may have any finite length, including zero.
\<close>

definition tick_role_entry_abs ::
  "'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "tick_role_entry_abs s =
     (let next = sa_tick s + 1;
          s0 = s\<lparr>sa_tick := next\<rparr>
      in if next = 0 then swap_delayed_roles s0 else s0)"

definition tick_due_sequence_abs ::
  "'tid scheduler_abs \<Rightarrow> 'tid node_kind list"
where
  "tick_due_sequence_abs s =
     (let entry = tick_role_entry_abs s;
          q = current_delayed_ring entry
      in due_nodes (sa_tick entry) q)"

lemma tick_role_entry_frames_physical_delayed_rings [simp]:
  "sa_delayed_a (tick_role_entry_abs s) = sa_delayed_a s \<and>
   sa_delayed_b (tick_role_entry_abs s) = sa_delayed_b s"
  by (simp add: tick_role_entry_abs_def swap_delayed_roles_def Let_def)

lemma tick_role_entry_wrap_role:
  assumes wrap: "sa_tick s + 1 = 0"
  shows
    "sa_current_role_a (tick_role_entry_abs s) =
       (\<not> sa_current_role_a s) \<and>
     sa_overflows (tick_role_entry_abs s) = Suc (sa_overflows s)"
  using wrap
  by (simp add: tick_role_entry_abs_def swap_delayed_roles_def Let_def)

lemma tick_role_entry_no_wrap_role:
  assumes no_wrap: "sa_tick s + 1 \<noteq> 0"
  shows
    "sa_current_role_a (tick_role_entry_abs s) = sa_current_role_a s \<and>
     sa_overflows (tick_role_entry_abs s) = sa_overflows s"
  using no_wrap
  by (simp add: tick_role_entry_abs_def Let_def)

definition tick_wake_one_abs ::
  "'tid node_kind \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid scheduler_abs"
where
  "tick_wake_one_abs n s =
     (case n of
        Event t \<Rightarrow> s
      | Generic t \<Rightarrow>
          let q = current_delayed_ring s;
              s0 = put_current_delayed (list_remove_abs (Generic t) q) s
          in add_ready_node (Generic t) s0)"

fun tick_wake_due_steps_abs ::
  "'tid node_kind list \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid scheduler_abs"
where
  "tick_wake_due_steps_abs [] s = s"
| "tick_wake_due_steps_abs (n # ns) s =
     tick_wake_due_steps_abs ns (tick_wake_one_abs n s)"

definition TickUnlockedDecomp ::
  "'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
where
  "TickUnlockedDecomp s t \<longleftrightarrow>
     (let entry = tick_role_entry_abs s;
          due = tick_due_sequence_abs s
      in t = tick_wake_due_steps_abs due entry)"

definition tick_due_loop_inv ::
  "'tid scheduler_abs \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
where
  "tick_due_loop_inv entry due done todo rest current \<longleftrightarrow>
     due = done @ todo \<and>
     ring (current_delayed_ring entry) = due @ rest \<and>
     distinct (due @ rest) \<and>
     (\<forall>n \<in> set (due @ rest). \<exists>t. n = Generic t) \<and>
     (\<forall>n \<in> set due.
        item_key (current_delayed_ring entry) n \<le> sa_tick entry) \<and>
     (case rest of
        [] \<Rightarrow> True
      | n # ns \<Rightarrow>
          sa_tick entry < item_key (current_delayed_ring entry) n) \<and>
     current = tick_wake_due_steps_abs done entry \<and>
     ring (current_delayed_ring current) = todo @ rest"

lemma tick_due_loop_inv_initial:
  assumes ring: "ring (current_delayed_ring entry) = due @ rest"
    and distinct: "distinct (due @ rest)"
    and generic:
      "\<forall>n \<in> set (due @ rest). \<exists>t. n = Generic t"
    and due_keys:
      "\<forall>n \<in> set due.
         item_key (current_delayed_ring entry) n \<le> sa_tick entry"
    and stop:
      "case rest of
         [] \<Rightarrow> True
       | n # ns \<Rightarrow>
           sa_tick entry < item_key (current_delayed_ring entry) n"
  shows "tick_due_loop_inv entry due [] due rest entry"
  using assms by (simp add: tick_due_loop_inv_def)

lemma tick_due_loop_inv_finished:
  assumes inv: "tick_due_loop_inv entry due done [] rest current"
  shows
    "done = due \<and>
     current = tick_wake_due_steps_abs due entry \<and>
     ring (current_delayed_ring current) = rest"
  using inv by (auto simp: tick_due_loop_inv_def)

text \<open>
  Concrete scalar/pointer transformer for the source prefix before the delayed
  loop.  On wrap it swaps only the two delayed-root pointer globals and
  increments the overflow counter; physical list objects themselves are not
  moved.
\<close>

definition scheduler_tick_role_entry_state ::
  "Scheduler_V611_Parse.globals \<Rightarrow> Scheduler_V611_Parse.globals"
where
  "scheduler_tick_role_entry_state c =
     (let next = Scheduler_V611_Parse.globals.xTickCount_' c + 1;
          c0 = Scheduler_V611_Parse.globals.xTickCount_'_update
            (\<lambda>_. next) c
      in if next = 0 then
           let current =
             Scheduler_V611_Parse.globals.pxDelayedTaskList_' c0;
               overflow =
             Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_' c0
           in Scheduler_V611_Parse.globals.xNumOfOverflows_'_update
                (\<lambda>n. n + 1)
              (Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_'_update
                (\<lambda>_. current)
               (Scheduler_V611_Parse.globals.pxDelayedTaskList_'_update
                 (\<lambda>_. overflow) c0))
         else c0)"

lemma scheduler_tick_role_entry_preserves_role_rel:
  assumes role: "scheduler_role_rel R c a"
    and tick:
      "Scheduler_V611_Parse.globals.xTickCount_' c = sa_tick a"
  shows
    "scheduler_role_rel R
       (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)"
  using role tick
  by (auto simp: scheduler_role_rel_def scheduler_tick_role_entry_state_def
      tick_role_entry_abs_def swap_delayed_roles_def Let_def)

text \<open>
  This is an actual generated-source leaf already proved for arbitrary valid
  rings and arbitrary member positions.  It is reusable for the generic-item
  removal and, when an event-root relation is supplied, for the conditional
  event-item removal in the delayed loop.
\<close>

theorem scheduler_tick_vListRemove_general_exact:
  fixes s :: Scheduler_V611_Parse.globals
    and lp :: "Scheduler_V611_Parse.xLIST_C ptr"
    and p :: "Scheduler_V611_Parse.xLIST_ITEM_C ptr"
  assumes rel:
      "raw_xlist_rel
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
        (abi_list_ptr lp) xs"
    and member: "abi_item_ptr p \<in> set (ring xs)"
  shows
    "Scheduler_V611_Delay_Translation.vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_mem_state
         (raw_remove_concrete_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
           (abi_item_ptr p)) s
     \<rbrace>"
  by (rule scheduler_vListRemove_general_exact_state[OF rel member])

definition scheduler_unlocked_tick_rep_rel ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
where
  "scheduler_unlocked_tick_rep_rel D R c a \<longleftrightarrow>
     scheduler_resume_rep_rel D R c a \<and>
     R = generated_scheduler_roots \<and>
     sa_suspend_depth a = 0"

text \<open>
  Honest handoff for the generated delayed loop.  The source summary remains
  an explicit premise because the current repository has no universal
  scheduler vListInsertEnd bridge and no representation for arbitrary event
  list roots.  Once those source effects prove TickUnlockedDecomp, this rule
  transfers the result without specializing the due prefix or wrap branch.
\<close>

theorem scheduler_vTaskIncrementTick_unlocked_summary:
  fixes PostRel ::
    "Scheduler_V611_Parse.globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
  assumes source_summary:
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
     \<lbrace>\<lambda>r t.
       \<exists>a'. r = Result () \<and>
         TickUnlockedDecomp a a' \<and> PostRel t a'
     \<rbrace>"
    and model_agreement:
      "\<And>a'. TickUnlockedDecomp a a' \<Longrightarrow>
         a' = tick_unlocked_abs a"
  shows
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and> PostRel t (tick_unlocked_abs a)
     \<rbrace>"
  apply (rule runs_to_weaken[OF source_summary])
  using model_agreement by blast

end
