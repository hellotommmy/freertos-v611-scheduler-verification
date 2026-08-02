# Source scope ledger

Status: final source and artifact scope boundary.  Build and theorem status is
recorded separately and does not enlarge this ledger.

## Paper-reported scope

The allowed ICFEM 2015 paper reports, excluding blank and comment lines:

- 17 core scheduler API functions in `tasks.c`: 361 LOC;
- 15 `xList` functions in `list.c`: 121 LOC;
- total verified implementation: 482 LOC.

The experiment counts physical lines in the actual executed dependency slice,
including required private helpers and concrete type/macro definitions.  It
does not add unrelated APIs merely to reach the requested range.

## Narrowed semantic roots and source-only closure

Roots:

- `vTaskDelayUntil`;
- `vTaskDelay`;
- `vTaskIncrementTick`;
- `vTaskSwitchContext`;
- `xTaskGetTickCount`.

The raw call/macro closure (before evaluating configuration branches) is:

- task bodies: `vTaskDelayUntil`, `vTaskDelay`, `vTaskSuspendAll`,
  `xTaskResumeAll`, `xTaskGetTickCount`, `vTaskIncrementTick`, and
  `vTaskSwitchContext`;
- list bodies: `vListInitialise`, `vListInitialiseItem`, `vListInsertEnd`,
  `vListInsert`, `vListRemove`;
- reached macros: `listGET_LIST_ITEM_VALUE`,
  `listGET_OWNER_OF_HEAD_ENTRY`, `listGET_OWNER_OF_NEXT_ENTRY`,
  `listLIST_IS_EMPTY`, `listSET_LIST_ITEM_OWNER`,
  `listSET_LIST_ITEM_VALUE`, `prvAddTaskToReadyQueue`,
  `prvCheckDelayedTasks` and the trace-off `vWriteTraceToBuffer` fallback.

Frozen lean configuration: both delay APIs enabled; trace, runtime statistics,
stack-overflow checks, tick hook, and MPU disabled; 32-bit tick retained.

## Frozen addressed-data projection

The external builder/generator extracts, relink-checks, and hash-locks a frozen
ELF/ledger/configuration chain for exactly six scheduler-list C bases.  The
patched CParser configuration definitionally fixes those addresses and admits
no other addressed-data base.  Isabelle does not prove the external
ELF-to-configuration correspondence.

| Mapped C base | Address | Size | Derived static `xLIST` regions | P2 use |
|---|---:|---:|---|---|
| `pxReadyTasksLists` | `0x00102020` | 80 | ready[0] `0x00102020`; ready[1] `0x00102034`; ready[2] `0x00102048`; ready[3] `0x0010205c` | four P2 roots |
| `xDelayedTaskList1` | `0x0010208c` | 20 | delayed-A `0x0010208c` | P2 root |
| `xDelayedTaskList2` | `0x001020a0` | 20 | delayed-B `0x001020a0` | P2 root |
| `xPendingReadyList` | `0x001020bc` | 20 | pending-ready `0x001020bc` | P2 root |
| `xSuspendedTaskList` | `0x001020d4` | 20 | suspended `0x001020d4` | P2 root |
| `xTasksWaitingTermination` | `0x001020e8` | 20 | termination-wait `0x001020e8` | mapped for exact CParser coverage; outside P2 |

Consequently the six mapped bases derive exactly nine pairwise separate
static `xLIST` regions.  The P2 relation and footprint use exactly eight of
them: the four ready-list elements, delayed-A, delayed-B, pending-ready, and
suspended.  The ninth, termination-wait, is included in the static-address
geometry and exact-map boundary but is deliberately not a P2 relation root.

The P2_IDLE and P2_RUN task control blocks are logical runtime objects in the
heap witness.  They are not additional fixed-address ELF symbols and are not
evidence that an allocator or the FreeRTOS boot path constructs those objects.

The evidence objects locking this projection are:

| Object | SHA-256 |
|---|---|
| frozen `frozen_p2_layout.elf` | `DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A` |
| `layout_ledger.json` | `CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02` |
| generated `P2_Root_Address_Config.ML` | `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712` |
| audited upstream AutoCorres2 `calculate_state.ML` | `EA51ECAA01947E53AD38A684B0E97ED360339363A75C6AE16DCFBA7713562898` |
| local addressed-global patch | `44160F97B133D0A66E515E505636D641907DC14811D43DA071EA15C706C8E604` |

Within this source/artifact boundary, the final proof inventory contains 13
source-to-abstract refinements over 8 distinct source operations, including 2
sequential compositions.  One composition is the literal
`vListInitialise' -> vListInitialiseItem' -> vListInsertEnd' ->
vListRemove'` chain: it has no assumptions, uses exactly three
`runs_to_bind` steps, and makes no `tail8` claim.  The artifact-bound P2
theorem executes the artifact-specialized generated `vTaskDelay' 2` exact state and reaches
the `YieldPending` refinement endpoint.  These theorem facts do not expand the
source slice or the explicit exclusions below.

Exact configuration-active, self-contained upstream semantic slice:

| File | Inclusive upstream line intervals | Physical |
|---|---|---:|
| `tasks.c` | 55-57, 62-68, 79-117, 129, 133-138, 154-155, 157, 159-162, 212-240, 250-257, 268-286, 602-676, 679-737, 1098-1103, 1106-1175, 1188-1200, 1397-1450, 1593-1640 | 444 |
| `list.c` | 55-57, 63-80, 83-87, 90-110, 113-167, 170-189 | 122 |
| `list.h` | 98-124, 142, 152, 161, 187-198, 217, 241, 252, 265, 286, 298 | 48 |
| `task.h` | 64-65, 485, 544, 895, 947, 973, 1172, 1235 | 9 |
| `FreeRTOS.h` | 61, 64, 67, 70, 229-233, 235-239, 355-357, 359-361, 379-381, 413-415 | 26 |
| `portable.h` | 306-308, 338 | 4 |
| `mpu_wrappers.h` | 59, 125-131 | 8 |
| `projdefs.h` | 60-61 | 2 |
| `StackMacros.h` | 73-79 | 7 |
| **Total** | union within each file | **670** |

The same union is 587 nonblank and 458 nonblank-noncomment lines.  This is a
provenance-bearing semantic source slice, not the whole translation unit.

## Frozen provenance fields

- official archive SHA-256:
  `9638ADBFAC481DAB5CFFA5BBE82EB22624D9811515C7216DE119B94E7C881F39`
- source files and hashes: frozen in `upstream/SHA256SUMS`;
- exact configuration-active line intervals: table above;
- configuration-active physical semantic LOC: 670;
- nonblank LOC: 587;
- nonblank/noncomment LOC: 458;
- full unmodified compile/CParser translation footprint (reported separately):
  5,603 physical / 4,660 nonblank / 2,274 nonblank-noncomment lines, excluding
  system headers;
- generated/preprocessor LOC (reported separately, never used to inflate the
  source total):
- license file SHA-256:
  `603E417E742EB34C3DF5EC67E9AF6C1FEA87226483B87608EFC850931191D2AC`.

The full upstream files are intentionally larger than the target slice:
`tasks.c` has 2,383 physical lines and `list.c` has 191.  The 500--800 LOC
gate is evaluated on the auditable semantic execution slice.  Tooling cost and
the whole-TU parser footprint remain first-class metrics rather than being
hidden inside or confused with target LOC.

## Explicit exclusions

This scope does not include allocator correctness, task-object construction,
boot/startup reachability, scheduler-start reachability, compiler correctness,
execution of the pending context switch, machine-code correctness,
binary-to-source equivalence, or execution of the frozen ELF.  It also does
not claim a deployed-port equivalence or full FreeRTOS scheduler functional
correctness.  The full translation unit is a parser/translation-support
footprint; it is not silently promoted into the 670-line semantic target or
into a whole-scheduler theorem.
