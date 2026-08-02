theory Scheduler_Generic_Root_Universe_Coverage
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Universe_Coverage_Core.Scheduler_Generic_Root_Universe_Coverage_Core"
begin

text \<open>
  Compatibility facade for the root-universe coverage development.  The
  checker-stable root enumeration and geometry live in the Base heap; the
  universally quantified Generic and Event family coverage interfaces live in
  the Coverage Core heap.
\<close>

end
