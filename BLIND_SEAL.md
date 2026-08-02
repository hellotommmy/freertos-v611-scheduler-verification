# Blind reconstruction seal

Seal date: 2026-08-01.

Status: `CHECKER_GREEN_FROZEN_P2_MILESTONE`.

This file seals the independently reconstructed FreeRTOS V6.1.1 list and
scheduler milestone described below.  It is an evidence index, not a claim of
whole-scheduler, binary, boot, allocator, or deployed-port correctness.  The
original VCC annotations, Z models, abstraction relation, invariants, proof
scripts, and supplementary proof artifact were not inputs to this blind
reconstruction.

Git commit, pull-request, and release identifiers are deliberately not guessed
here.  They are publication metadata and must be recorded only after those
objects exist.  The completed PDF is recorded below; none of this publication
metadata changes the theorem scope recorded by this seal.

## Publication document

| Object | SHA-256 |
|---|---|
| `output/pdf/freertos_v611_p2_mathematical_progress.pdf` | `87C83CAFD59D45ACD8E92FF7CD4961B165B688E97F57CFAF47E95D5CC82B1D60` |

The PDF is seven A4 pages.  It was rendered from the checked mathematical
progress manuscript and visually inspected page by page; text extraction finds
no empty page or Unicode replacement character.

## Sealed result

The literal alias-sensitive source-monad chain
`vListInitialise' -> vListInitialiseItem' -> vListInsertEnd' -> vListRemove'`
is kernel-green without theorem premises.  Separately, the external builder
and generator extract, relink-check, and hash-lock six scheduler-list addresses
from one frozen ELF32 artifact.  The generated configuration definitionally
fixes those bases in the artifact-specialized CParser/AutoCorres2 source
semantics; the bases derive nine static `xLIST` regions, of which eight are the
P2 relation roots.  A concrete heap witness uses two fresh logical runtime TCB
addresses, establishes the P2 endpoint and footprint, and discharges the
premises of the generated `vTaskDelay' (2 :: 32 word)` source-to-abstract
refinement theorem.  The external ELF-to-configuration evidence link is not
an Isabelle theorem or a source-to-binary proof.

Every final Isabelle run in this file has `exit_code=0`,
`quick_and_dirty=false`, and `timed_out=false`.  The seal contains no generated
theorem skeleton and relies on no admitted proof command.

## Portable artifact and parser lock

All values below are SHA-256 hashes recomputed from the final files on disk.
The artifact and generated-manifest hashes are deterministic locks; status and
stdout hashes later in this file identify the particular bounded replay and
are not asserted to be identical on a different host.

| Object | SHA-256 |
|---|---|
| official FreeRTOS V6.1.1 archive | `9638ADBFAC481DAB5CFFA5BBE82EB22624D9811515C7216DE119B94E7C881F39` |
| upstream `Source/tasks.c` | `0A5B6C12AEA6FAE2A951C0E80BDC301C646EF8C6360D574A2C4699D4C33A45BF` |
| upstream `Source/list.c` | `EEAD2C4F6AEB2DA0CF4A5606EC4A213EF492B09C12DF1A0097B6442688C82ABB` |
| upstream AutoCorres2 `c-parser/calculate_state.ML` | `EA51ECAA01947E53AD38A684B0E97ED360339363A75C6AE16DCFBA7713562898` |
| `patches/autocorres2-addressed-global-definitions.patch` | `44160F97B133D0A66E515E505636D641907DC14811D43DA071EA15C706C8E604` |
| staged patched `c-parser/calculate_state.ML` | `FD244D8228E79EC3626A5CE312446CE49DF550970B758B68D3BBE953CAC8CFA9` |
| `artifacts/frozen_p2_layout/output/frozen_p2_layout.elf` | `DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A` |
| `artifacts/frozen_p2_layout/output/layout_ledger.json` | `CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02` |
| `build/generated/P2_Root_Address_Config.ML` | `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712` |

The ledger records a deterministic relink match and a canonical project root
of `/workspace/freertos_v611_scheduler`.  The patched parser rejects malformed,
duplicate, out-of-range, missing, or extra addressed-data definitions and
requires exact coverage of the CParser-discovered addressed globals.

## Portable proof-source lock

| Object | SHA-256 |
|---|---|
| `scripts/build-list-smoke.ps1` | `3C8D79822E9F0C32D0FDC17782CB2526DDEB2F7F39A2E6AC32ABF34815C6A1B1` |
| `theories/ROOT` | `AED02E98B974304466E543864365D9AB0E94FE430A91720B8BF4587BBF1FCE27` |
| `theories/scheduler_parse/Scheduler_V611_Parse.thy` | `ADF5014F4FD55FC46A25C1C84A6F4C0D129AD65215D4B2B9B3904DDD38E94A95` |
| `theories/scheduler_p2_layout_no_go/Scheduler_P2_Layout_No_Go.thy` | `82F39339020F8CB4766322C663922B64785F79CA62AFB649D87C0B837A067C57` |
| `theories/scheduler_p2_frozen_static_layout/Scheduler_P2_Frozen_Static_Layout.thy` | `1E7D9A465ED4760913DC40BF1E9D826EF22A3BA01DCDB68C56BB74BA69E2563D` |
| `theories/scheduler_p2_frozen_dynamic_geometry/Scheduler_P2_Frozen_Dynamic_Geometry.thy` | `00D2FE13142BEC28B9243580760EF763D676EDDF873EDCFE971DF27D9FCC2039` |
| `theories/scheduler_p2_frozen_preimage/Scheduler_P2_Frozen_Preimage.thy` | `DBAA86A8D645C291F67F417645AC170E71EBCE6293CA458E90D153EA5E836A83` |
| `theories/scheduler_p2_delay_source/Scheduler_P2_Delay_Source.thy` | `7BFB623FE099104EA4276D0119CCD6C7B23A0F94ABF04B87FAAFAF3AEB1DD6C0` |
| `theories/scheduler_p2_post_relation/Scheduler_P2_Post_Relation.thy` | `CF5CCB728150BC4B185CEAE448E9E2FAB0C9C88E1CCBCDA1F79E2A67AD7375B8` |
| `theories/scheduler_p2_delay_refinement/Scheduler_P2_Delay_Refinement.thy` | `43BC41254C609DF8302F38113F662912E2FD99C72D0A612E5A72925E5AA1C9E7` |
| `theories/list_raw_r6_initialise_insert_remove_sequence/List_V611_Raw_R6_Initialise_Insert_Remove_Sequence.thy` | `279B203FED23C9E23F6285D993A599EB925670E71267A1B1ECE51336CD1025CD` |
| `theories/list_smoke/List_V611_Translation.thy` | `EAF619B1DE3FC8854F60F0D0E2DBAA2ED58490E452CA67F86EEB7489FC8F5E60` |
| `theories/list_raw_skip/List_V611_Raw_Skip_Translation.thy` | `73D8EC3AF7D108203DF143981286EC4CFFCCEC1230101D6A760161AD4725D7CD` |
| `theories/capstone_assumption_audit/Capstone_Assumption_Audit.thy` | `3EEA7EA0AF579112D875FD68BECBFF2DBA07DE4942E06766F2E074E3BE9CDCF0` |

## Six bases, nine static regions, eight P2 roots

The exact addressed-data map is:

| Mapped C base | Address | Size | Derived `xLIST` regions | P2 relation use |
|---|---:|---:|---|---|
| `pxReadyTasksLists` | `0x00102020` | 80 | ready[0] `0x00102020`, ready[1] `0x00102034`, ready[2] `0x00102048`, ready[3] `0x0010205c` | four roots |
| `xDelayedTaskList1` | `0x0010208c` | 20 | delayed-A | one root |
| `xDelayedTaskList2` | `0x001020a0` | 20 | delayed-B | one root |
| `xPendingReadyList` | `0x001020bc` | 20 | pending-ready | one root |
| `xSuspendedTaskList` | `0x001020d4` | 20 | suspended | one root |
| `xTasksWaitingTermination` | `0x001020e8` | 20 | termination-wait | exact parser coverage only |

Thus the invariant is exactly **six mapped bases -> nine static `xLIST`
regions -> eight P2 relation roots**.  The ninth region, termination-wait, is
included in the all-addressed geometry and in the exact CParser map but not in
the P2 endpoint relation.

The P2 heap witness chooses `P2_IDLE` at logical TCB address `0x00200000` and
`P2_RUN` at logical TCB address `0x00200100`.  Their 68-byte TCB regions and
embedded generic/event list-item regions are guarded, mutually separated, and
separated from all nine static list regions.  They are logical runtime witness
objects, not ELF symbols, not linker outputs, and not evidence of allocation or
boot construction.

## Core checked theorem inventory

The key theorem chain is:

- stock-layout obstruction:
  `p2_source_footprint_delayed_alias_no_go`;
- exact generated addressed pointers and static geometry:
  `frozen_addressed_global_pointers`,
  `frozen_addressed_xlist_geometry`, and
  `frozen_p2_static_root_geometry`;
- fresh logical TCB and embedded-item geometry:
  `frozen_p2_tcb_addressed_xlist_separation` and
  `frozen_p2_nonheap_geometry`;
- artifact-specialized generated P2 source execution and abstraction:
  `scheduler_vTaskDelay_2_p2_exact_state`,
  `p2_remove_wake_insert_lists_rel`, and
  `scheduler_vTaskDelay_2_p2_refines_task_delay_abs`;
- concrete artifact-bound endpoint, non-vacuity, and closed refinement:
  `frozen_p2_endpoint`,
  `frozen_p2_preimage_nonempty`,
  `frozen_p2_artifact_bound_vTaskDelay_2_refinement`, and
  `frozen_p2_artifact_bound_seal`;
- literal four-call list chain:
  `raw_vListInitialise_insert_end_remove_refines` and
  `raw_vListInitialise_insert_end_remove_empty_refines`.

The final `frozen_p2_artifact_bound_seal` has no premises.  It existentially
packages a decoder, root record, and concrete C state satisfying the P2
endpoint and footprint, together with normal execution of the generated
`vTaskDelay' 2` body to the abstract `task_delay_abs 2 p2_pre` endpoint.

The dedicated leaf `Capstone_Assumption_Audit` checks this seal, its nonempty
preimage and refinement components, and both four-call capstones directly as
kernel theorem objects.  For all five, `Thm.prems_of` and `Thm.hyps_of` are
empty, the proposition contains no `Pure.imp` or `HOL.implies`, and both sort-
hypothesis counts are zero.  Therefore no function-address,
addressed-data-global, or generated `G`/`S` locale premise survives.  The
fail-closed details are recorded in `ASSUMPTION_AUDIT.md`.

## Exact refinement count: 13 / 8 / 2

The strict source-to-abstract theorem inventory contains **13** theorems over
**8** distinct source operations, including **2** source-monad sequential
composition theorems:

1. `raw_vListInsertEnd_empty_refines`;
2. `raw_vListRemove_singleton_refines`;
3. `raw_vListRemove_general_refines`;
4. `xTaskGetTickCount_refines`;
5. `vTaskSwitchContext_suspended_refines`;
6. `vTaskIncrementTick_suspended_refines`;
7. `vTaskDelay_zero_refines`;
8. `vTaskDelayUntil_suspended_no_delay_refines`;
9. `raw_vListInsertEnd_general_refines_via_transformer`;
10. `raw_vListRemove_insert_end_general_refines` (sequential composition);
11. `raw_vListInsert_ordered_empty_refines`;
12. `frozen_p2_artifact_bound_vTaskDelay_2_refinement`;
13. `raw_vListInitialise_insert_end_remove_refines` (sequential composition).

The eight distinct operations are `vListInsertEnd`, `vListRemove`,
`vListInsert`, `xTaskGetTickCount`, `vTaskSwitchContext`,
`vTaskIncrementTick`, `vTaskDelay`, and `vTaskDelayUntil`.  Fixed/general
variants, P2 strengthening of `vTaskDelay`, and sequential compositions do not
inflate the distinct-operation count.

## Literal four-call hard gate

`raw_initialise_insert_remove_needle'` is definitionally the four generated
source calls in order:

```text
vListInitialise' 0x00001000
vListInitialiseItem' 0x00002000
vListInsertEnd' 0x00001000 0x00002000
vListRemove' 0x00002000
```

The embedded sentinel address is `0x00001008`.  The public theorem
`raw_vListInitialise_insert_end_remove_refines` has no assumptions and its
proof contains exactly three `runs_to_bind` applications, the number required
to compose four calls.  It establishes normal `Result ()` execution and an
abstract `raw_xlist_rel` round trip; the clean corollary returns to an empty
abstract list.

This theorem deliberately makes **no `tail8` postcondition claim**.  Existing
tail-frame lemmas elsewhere are not silently promoted into the literal
four-call theorem.

## Final bounded Isabelle replay

| Run ID | Session | Exit | QAD | Timed out | Elapsed (s) | `status.txt` SHA-256 | `stdout.log` SHA-256 |
|---|---|---:|---|---|---:|---|---|
| `20260801Tseal-scheduler-parse-01-portable` | `EAL6_FreeRTOS_V611_Scheduler_Parse` | 0 | false | false | 23.566 | `F298A91A14C19386307589D140ECB3D0298F78BBF989C9768D632AA3F6A304F2` | `36AA4AE5EDA156D123DAAC5A53A5DB76CC5C817B8B7B8F9378163E9C94A3363D` |
| `20260801Tseal-p2-layout-no-go-01-portable` | `EAL6_FreeRTOS_V611_Scheduler_P2_Layout_No_Go` | 0 | false | false | 33.162 | `7B72F0727D91C1F6E1D67045D14BB666A9C02C8257A599672C329F4930073AC2` | `286AF01D88A5007CECBD1860739AE206F1A5083220501E9088054B1A412A1DF9` |
| `20260801Tseal-p2-static-nine-01-portable` | `EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Static_Layout` | 0 | false | false | 27.701 | `6916C72A9D7C92AF4337FA7AB805D949B8DAEAED39FF19C4C961E438D31E2238` | `BB442ECA20CE4753278CC884B79E403BC1EC0B82DAE7843A5AC5B68F0B2130C5` |
| `20260801Tseal-p2-dynamic-all-nine-01-portable` | `EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Dynamic_Geometry` | 0 | false | false | 27.467 | `E246B0B3A71817D5F76FB17F426A7F9B41B600ED19DFACEA9EE77D5B6FE87757` | `BB442ECA20CE4753278CC884B79E403BC1EC0B82DAE7843A5AC5B68F0B2130C5` |
| `20260801Tseal-p2-preimage-06-parenthesised-seal` | `EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Preimage` | 0 | false | false | 120.854 | `54D8D243FAA3F97786C2F8D27477CF03846D71EEBC53388F4B593099C9B69806` | `1E51B030BD7D73DD4491CDA05712ED099BEAD1D340F64C96242CD7E168B902CC` |
| `20260801Tseal-list-four-call-01-portable` | `EAL6_FreeRTOS_V611_List_Raw_R6_Initialise_Insert_Remove_Sequence` | 0 | false | false | 32.338 | `AC47CE2744C1F1212623CCD96A449CB916651E85E4F70225245072DE3630A7CA` | `B71D9682664FF9E68DBB2F93EE195DF4AB50BFD9CA6A2B62CE444FC10D6F427C` |
| `20260801Tseal-list-smoke-01-portable` | `EAL6_FreeRTOS_V611_List_Smoke` | 0 | false | false | 67.973 | `CBD81B8276144F834465720CC35E3631034B8CD070ACA98E4DE666CC0A6605BD` | `6AC96C1B4CEB3730C52572D732833E79556009D5B20B283B3C7DB7EE73A3B742` |
| `20260801Tseal-list-raw-skip-01-portable` | `EAL6_FreeRTOS_V611_List_Raw_Skip` | 0 | false | false | 22.551 | `6E12E351EECAE34A3633E85F254F9DA852EA84609E8C2E723F0C7CD6F07FF65B` | `709A280E7B197A72C59E7A07CCE99CF770A1A6E7BE472B34C890F7FFED895446` |
| `20260801Tseal-assumption-audit-01-portable` | `EAL6_FreeRTOS_V611_Capstone_Assumption_Audit` | 0 | false | false | 137.387 | `D9E5AED444D114B35EE1A07B6C67DEA58F5992AA864F93645AF7105517BFBF94` | `9186E921B5881C9412AE3FEB98CBAECF92A1E2E734F3A1344D9AEBF4CB88B1C3` |

The final forbidden-pattern scan at seal construction returned zero matches.
It must be rerun after any proof, proof-port, script, or patch change.

## Explicit exclusions and trust boundary

This seal does **not** establish:

- allocator correctness or that an allocator creates the two logical TCBs;
- task-object construction, client-task execution, boot reachability,
  scheduler-start reachability, or scheduler-caller composition;
- interrupt arrival inside an API or context-switch/port assembly execution;
- compiler, assembler, linker, loader, CParser, AutoCorres2, Isabelle, or
  Poly/ML correctness;
- source-to-binary equivalence, machine-code correctness, execution of the
  frozen ELF, or deployed-port equivalence;
- general/nonempty ordered insertion, nonmember removal, the blocking
  list-migration branch of `vTaskDelayUntil`, or unlocked branches of switch
  and tick increment; or
- complete scheduler functional correctness or whole-FreeRTOS verification.

The fixed-address ELF is static layout evidence only and is never executed.
Its link to the generated definitions is externally regenerated and validated,
not internalised as an Isabelle theorem.  The proof is relative to the audited
proof port and the artifact-specialized CParser / AutoCorres2 source semantics
checked by Isabelle.

## Reproduction commands

Run from the repository root in PowerShell.  The wrapper serializes builds,
forces `quick_and_dirty=false`, rebuilds and checks the frozen artifact,
regenerates the address configuration, verifies/applies the project-local
parser patch, and records each bounded run under a fresh ID.

```powershell
$stamp = [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssZ')
$sealSessions = @(
    @{ Session = 'EAL6_FreeRTOS_V611_Scheduler_Parse'; Timeout = 600 },
    @{ Session = 'EAL6_FreeRTOS_V611_Scheduler_P2_Layout_No_Go'; Timeout = 600 },
    @{ Session = 'EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Static_Layout'; Timeout = 600 },
    @{ Session = 'EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Dynamic_Geometry'; Timeout = 600 },
    @{ Session = 'EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Preimage'; Timeout = 1200 },
    @{ Session = 'EAL6_FreeRTOS_V611_List_Raw_R6_Initialise_Insert_Remove_Sequence'; Timeout = 1200 },
    @{ Session = 'EAL6_FreeRTOS_V611_List_Smoke'; Timeout = 600 },
    @{ Session = 'EAL6_FreeRTOS_V611_List_Raw_Skip'; Timeout = 600 },
    @{ Session = 'EAL6_FreeRTOS_V611_Capstone_Assumption_Audit'; Timeout = 1200 }
)

$index = 0
foreach ($entry in $sealSessions) {
    $index += 1
    $runId = '{0}-seal-replay-{1:D2}' -f $stamp, $index
    & .\scripts\build-list-smoke.ps1 `
        -Session $entry.Session `
        -TimeoutSeconds $entry.Timeout `
        -RunId $runId
    if ($LASTEXITCODE -ne 0) {
        throw "Isabelle seal replay failed: $($entry.Session)"
    }
}
```

Validate the scope ledger, exact source-to-ITP mapping, generator fail-closed
tests, and other project unit tests:

```powershell
python .\tools\verify_scope_manifest.py
python .\tools\validate_source_itp_mapping.py
python -m unittest discover -s tools -p 'test_*.py'
```

Run the final forbidden-pattern gate:

```powershell
$forbidden = rg -n -i `
    --glob '*.thy' --glob '*.ML' --glob '*.c' --glob '*.h' `
    --glob '*.ps1' --glob '*.patch' `
    '\b(sorry|oops|admit|axiomatization|oracle|skip_proof|cheat)\b|quick_and_dirty\s*=\s*true' `
    theories proof_port scripts patches

if ($LASTEXITCODE -notin @(0, 1)) {
    throw 'Forbidden-pattern scan itself failed'
}
if ($forbidden) {
    $forbidden
    throw 'Forbidden proof pattern found'
}
```

Finally run `git diff --check` and record the publication commit/PR/PDF hashes
only after those objects have actually been produced.
