theory Scheduler_One_Due_Task_Phases
  imports
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Generated.Scheduler_One_Due_Task_Phases_Generated"
begin

text \<open>
  Compatibility facade for the original one-due-task theory name.  The
  development is split across stable parent heaps so that proof repair in a
  generated leaf does not replay the pure phase model and representation
  bridge inside the same 120-second checker job.
\<close>

end
