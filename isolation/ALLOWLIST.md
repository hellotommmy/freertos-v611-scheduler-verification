# Blind-phase material allowlist

Only the following material classes may inform the reconstruction:

1. Official, unannotated FreeRTOS V6.1.1 release source and license:
   `https://sourceforge.net/projects/freertos/files/FreeRTOS/V6.1.1/`
2. Official/public FreeRTOS V6.1.1 user documentation and release notes.
3. The paper *Refinement-Based Verification of the FreeRTOS Scheduler in
   VCC* (ICFEM 2015), including its reported scope/cost and prose discussion:
   `https://eprints.whiterose.ac.uk/id/eprint/94516/1/refinement_based_verification.pdf`
4. Generic Isabelle/HOL, AFP AutoCorres2, C semantics, testing, and symbolic
   execution documentation that is not part of the FreeRTOS proof artifact.
5. Files created inside this experiment from the above materials.

The paper is deliberately allowed even where it discusses modelling choices;
every such influence is logged as paper exposure, so the result is blind to
the original formalization artifact, not blind to the published paper.

