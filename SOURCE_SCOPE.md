# Source scope ledger

Status: conditional freeze; configuration-active and translation-support
measurements remain pending the C translation needle.

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

## Pending freeze fields

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
