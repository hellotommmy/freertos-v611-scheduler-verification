theory Capstone_Assumption_Audit
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Preimage.Scheduler_P2_Frozen_Preimage"
    "EAL6_FreeRTOS_V611_List_Raw_R6_Initialise_Insert_Remove_Sequence.List_V611_Raw_R6_Initialise_Insert_Remove_Sequence"
begin

text \<open>
  This leaf theory is a fail-closed archival audit of the five sealed
  capstones.  It checks the theorem objects themselves, rather than relying on
  how their surface statements happen to print.  In particular, no theorem may
  retain a rule premise, a proof-context hypothesis, or a meta/object
  implication anywhere in its proposition.  The last check excludes a hidden
  global-address equation packaged as an implication premise.

  Sort hypotheses are counted and reported separately.  They encode type-class
  constraints and are not locale or program-state premises.
\<close>

ML \<open>
  val audited_capstones : (string * thm) list =
    [
      ("raw_vListInitialise_insert_end_remove_refines",
        @{thm raw_vListInitialise_insert_end_remove_refines}),
      ("raw_vListInitialise_insert_end_remove_empty_refines",
        @{thm raw_vListInitialise_insert_end_remove_empty_refines}),
      ("frozen_p2_preimage_nonempty",
        @{thm frozen_p2_preimage_nonempty}),
      ("frozen_p2_artifact_bound_vTaskDelay_2_refinement",
        @{thm frozen_p2_artifact_bound_vTaskDelay_2_refinement}),
      ("frozen_p2_artifact_bound_seal",
        @{thm frozen_p2_artifact_bound_seal})
    ]

  fun contains_implication (Const (name, _) $ lhs $ rhs) =
        name = "Pure.imp" orelse name = "HOL.implies" orelse
        contains_implication lhs orelse contains_implication rhs
    | contains_implication (lhs $ rhs) =
        contains_implication lhs orelse contains_implication rhs
    | contains_implication (Abs (_, _, body)) = contains_implication body
    | contains_implication _ = false

  fun pretty_terms ctxt terms =
    Pretty.string_of
      (Pretty.big_list "" (map (Syntax.pretty_term ctxt) terms))

  fun require_empty ctxt field theorem_name terms =
    if null terms then ()
    else
      error
        ("ASSUMPTION_AUDIT_FAILED theorem=" ^ theorem_name ^
         " field=" ^ field ^ " values=" ^ pretty_terms ctxt terms)

  fun audit_capstone ctxt (theorem_name, theorem_value) =
    let
      val premises = Thm.prems_of theorem_value
      val hypotheses = Thm.hyps_of theorem_value
      val proposition = Thm.prop_of theorem_value
      val sort_hypotheses = Thm.shyps_of theorem_value
      val extra_sort_hypotheses = Thm.extra_shyps theorem_value
      val _ = require_empty ctxt "Thm.prems_of" theorem_name premises
      val _ = require_empty ctxt "Thm.hyps_of" theorem_name hypotheses
      val _ =
        if contains_implication proposition then
          error
            ("ASSUMPTION_AUDIT_FAILED theorem=" ^ theorem_name ^
             " field=proposition implication=present")
        else ()
      val _ =
        writeln
          ("ASSUMPTION_AUDIT_OK theorem=" ^ theorem_name ^
           " prems=0 hyps=0 implications=0 shyps=" ^
           Int.toString (length sort_hypotheses) ^
           " extra_shyps=" ^
           Int.toString (length extra_sort_hypotheses))
    in
      ()
    end

  val _ = List.app (audit_capstone @{context}) audited_capstones
\<close>

end
