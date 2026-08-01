theory List_V611_Raw_R6_Ordered_Probe
  imports "EAL6_FreeRTOS_V611_List_Raw_Skip.List_V611_Raw_Skip_Translation"
begin

text \<open>
  Front-end availability probe for the stock V6.1.1 ordered insertion routine.
  This theory deliberately proves nothing: it only asks Isabelle to print the
  AutoCorres-generated monadic definition so that later invariant work starts
  from the checked translation rather than a guessed control-flow shape.
\<close>

print_statement vListInsert'_def

end
