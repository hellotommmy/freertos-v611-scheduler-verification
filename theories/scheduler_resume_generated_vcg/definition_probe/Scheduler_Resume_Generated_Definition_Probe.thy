theory Scheduler_Resume_Generated_Definition_Probe
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Outer_Scaffold.Scheduler_Resume_Outer_Scaffold"
begin

text \<open>
  Diagnostic export of the exact AutoCorres term.  This is used to name the
  generated pending-loop condition and body without guessing their state
  parameter or source-order bind structure.
\<close>

ML \<open>
  val ctxt = @{context};
  val source_def =
    @{thm Scheduler_V611_Delay_Translation.xTaskResumeAll'_def};
  val rendered =
    Pretty.string_of (Thm.pretty_thm ctxt source_def)
    |> YXML.parse_body
    |> XML.content_of;
  val _ =
    Export.export @{theory}
      (Path.binding0 (Path.make ["diagnostics", "xTaskResumeAll_def.txt"]))
      [XML.Text rendered];
\<close>

end
