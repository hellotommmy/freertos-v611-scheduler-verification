theory Scheduler_V611_Tick_Read_Refinement
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Tick.Scheduler_V611_Tick_Translation"
    "EAL6_FreeRTOS_V611_Scheduler_Abstract_Model.Scheduler_Abstract_Model"
begin

text \<open>
  First scheduler source-to-abstract needle.  At a quiescent API boundary the
  proof port is outside a critical section.  xTaskGetTickCount must return the
  committed source tick, restore the observable proof-port state, and leave
  the same pure scheduler state represented.  Missed ticks are deliberately
  not included: the source API reads xTickCount only.
\<close>

definition scheduler_tick_boundary_rel ::
  "globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
where
  "scheduler_tick_boundary_rel c a \<longleftrightarrow>
     xTickCount_' c = sa_tick a \<and>
     eal6_port_critical_depth_' c = 0 \<and>
     eal6_port_interrupts_disabled_' c = 0"

theorem xTaskGetTickCount_refines_committed_tick:
  assumes rel: "scheduler_tick_boundary_rel c a"
  shows
    "xTaskGetTickCount' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result (sa_tick a) \<and>
       scheduler_tick_boundary_rel t a
     \<rbrace>"
proof -
  have tick: "xTickCount_' c = sa_tick a"
    using rel by (simp add: scheduler_tick_boundary_rel_def)
  have depth: "eal6_port_critical_depth_' c = 0"
    using rel by (simp add: scheduler_tick_boundary_rel_def)
  have interrupts: "eal6_port_interrupts_disabled_' c = 0"
    using rel by (simp add: scheduler_tick_boundary_rel_def)
  show ?thesis
    unfolding xTaskGetTickCount'_def
      eal6_port_enter_critical'_def eal6_port_exit_critical'_def
      scheduler_tick_boundary_rel_def
    apply runs_to_vcg
    apply (simp_all add: tick depth interrupts)
    done
qed

theorem xTaskGetTickCount_refines:
  assumes rel: "scheduler_tick_boundary_rel c a"
  shows
    "xTaskGetTickCount' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result (fst (task_get_tick_abs a)) \<and>
       scheduler_tick_boundary_rel t (snd (task_get_tick_abs a))
     \<rbrace>"
  using xTaskGetTickCount_refines_committed_tick[OF rel]
  by simp

end
