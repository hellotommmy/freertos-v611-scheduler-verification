# Capstone assumption audit

## Purpose

The final archival correction asks whether any sealed capstone still carries
function-address, addressed-data-global, or generated `G`/`S` locale
assumptions.  A dedicated Isabelle leaf session answers that question directly
from the kernel theorem objects.

## Fail-closed method

Session `EAL6_FreeRTOS_V611_Capstone_Assumption_Audit` imports both independent
capstone sessions and audits these five theorem values at build time:

- `raw_vListInitialise_insert_end_remove_refines`
- `raw_vListInitialise_insert_end_remove_empty_refines`
- `frozen_p2_preimage_nonempty`
- `frozen_p2_artifact_bound_vTaskDelay_2_refinement`
- `frozen_p2_artifact_bound_seal`

For each theorem, the ML checker aborts the Isabelle build unless both
`Thm.prems_of` and `Thm.hyps_of` are empty.  It also traverses the complete
proposition and rejects any `Pure.imp` or `HOL.implies`, including implications
under binders or postcondition lambdas.  Therefore an addressed-global
equality cannot survive as an implication premise merely because it is nested
below the outer proposition.

The checker reports `Thm.shyps_of` and `Thm.extra_shyps` counts separately.
Sort hypotheses, if present, are type-class constraints; they are not locale,
heap-state, function-address, or `G`/`S` premises and are not rejected.

## Result

The single final portable replay was
`20260801Tseal-assumption-audit-01-portable`.  It built session
`EAL6_FreeRTOS_V611_Capstone_Assumption_Audit` with
`quick_and_dirty=false`, exited 0, did not time out, and completed in 137.387
seconds.  The session's exported `PIDE/messages` contains one
`ASSUMPTION_AUDIT_OK` record per theorem with these exact counts:

| Theorem | `prems` | `hyps` | implications | `shyps` | `extra_shyps` |
|---|---:|---:|---:|---:|---:|
| `raw_vListInitialise_insert_end_remove_refines` | 0 | 0 | 0 | 0 | 0 |
| `raw_vListInitialise_insert_end_remove_empty_refines` | 0 | 0 | 0 | 0 | 0 |
| `frozen_p2_preimage_nonempty` | 0 | 0 | 0 | 0 | 0 |
| `frozen_p2_artifact_bound_vTaskDelay_2_refinement` | 0 | 0 | 0 | 0 | 0 |
| `frozen_p2_artifact_bound_seal` | 0 | 0 | 0 | 0 | 0 |

Thus none of the five theorem objects retains a function-address,
addressed-data-global, `G`, or `S` locale premise.  No type-class sort
hypotheses are present either.  The theory itself is the fail-closed source of
truth: a zero exit is impossible if any audited theorem has a rule premise,
proof-context hypothesis, or implication in its proposition.

The run's recorded stdout SHA-256 is
`9186E921B5881C9412AE3FEB98CBAECF92A1E2E734F3A1344D9AEBF4CB88B1C3`;
its `status.txt` SHA-256 is
`D9E5AED444D114B35EE1A07B6C67DEA58F5992AA864F93645AF7105517BFBF94`;
stderr is empty and has SHA-256
`7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6`.
The audited leaf theory's SHA-256 is
`3EEA7EA0AF579112D875FD68BECBFF2DBA07DE4942E06766F2E074E3BE9CDCF0`.

## Boundary

This audit establishes assumption-freedom of the five named theorem objects.
It does not expand their conclusions: the frozen P2 results retain their stated
artifact/source-level scope and do not claim allocator or boot reachability,
context-switch execution, compiler correctness, binary correctness, or full
scheduler functional correctness.
