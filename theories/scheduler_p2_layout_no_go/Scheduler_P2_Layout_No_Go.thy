theory Scheduler_P2_Layout_No_Go
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Source_Footprint.Scheduler_P2_Source_Footprint"
begin

text \<open>
  A source footprint already commits to eight distinct physical scheduler
  roots.  These lemmas expose the corresponding layout obstruction without
  adding a new address assumption or attempting to instantiate a heap.
\<close>

lemma p2_source_footprint_physical_roots_distinctD:
  assumes footprint:
    "p2_source_footprint D generated_scheduler_roots h"
  shows "distinct (p2_physical_roots generated_scheduler_roots)"
  using footprint
  by (simp add: p2_source_footprint_def)

lemma p2_source_footprint_delayed_roots_distinctD:
  assumes footprint:
    "p2_source_footprint D generated_scheduler_roots h"
  shows
    "Scheduler_V611_Parse.xDelayedTaskList1_' \<noteq>
     Scheduler_V611_Parse.xDelayedTaskList2_'"
proof -
  have roots:
    "distinct (p2_physical_roots generated_scheduler_roots)"
    by (rule p2_source_footprint_physical_roots_distinctD[OF footprint])
  show ?thesis
    using roots
    by (simp add: p2_physical_roots_def generated_scheduler_roots_def)
qed

theorem p2_source_footprint_delayed_alias_no_go:
  assumes roots_alias:
    "Scheduler_V611_Parse.xDelayedTaskList1_' =
     Scheduler_V611_Parse.xDelayedTaskList2_'"
  shows
    "\<not> (\<exists>D h.
       p2_source_footprint D generated_scheduler_roots h)"
proof
  assume witness:
    "\<exists>D h. p2_source_footprint D generated_scheduler_roots h"
  then obtain D h where
    footprint:
      "p2_source_footprint D generated_scheduler_roots h"
    by blast
  have distinct:
    "Scheduler_V611_Parse.xDelayedTaskList1_' \<noteq>
     Scheduler_V611_Parse.xDelayedTaskList2_'"
    by (rule p2_source_footprint_delayed_roots_distinctD[OF footprint])
  show False
    using roots_alias distinct by contradiction
qed

end
