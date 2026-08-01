# Scheduler trace harness design

Status: `EXTENDED_SOURCE_TRACE_DELAY_PHASES_GREEN`

This harness is an independent source-level experiment.  It does not inspect
an original formalisation and does not modify the frozen FreeRTOS V6.1.1
archive.

## Composition boundary

`scheduler_trace.c` directly includes, in the same load-bearing order as the
proof translation unit:

1. `proof_port/scheduler/scheduler_port_contract.c`;
2. untouched upstream `Source/tasks.c`;
3. untouched upstream `Source/list.c`.

Being in one C translation unit lets the harness observe the scheduler's
file-static lists and counters without deleting `static`, adding test hooks, or
copying scheduler bodies.  Scenario construction calls the upstream
`prvInitialiseTaskLists`, `vListInitialiseItem`, `vListInsert`, and
`prvAddTaskToReadyQueue` operations; the transitions under test call the
upstream `vTaskIncrementTick`, `vTaskSwitchContext`, and `vTaskDelay` bodies.

The archived hashes observed by the green run remain:

| File | SHA-256 |
|---|---|
| `Source/tasks.c` | `0A5B6C12AEA6FAE2A951C0E80BDC301C646EF8C6360D574A2C4699D4C33A45BF` |
| `Source/list.c` | `EEAD2C4F6AEB2DA0CF4A5606EC4A213EF492B09C12DF1A0097B6442688C82ABB` |

## Host ABI boundary

The proof port uses C `long` on a 32-bit StrictCParser machine.  WSL GCC is
LP64, so compiling the proof spelling literally would make `portTickType`
64-bit and `0xffffffffUL + 1` would not wrap.  The harness therefore mirrors
the proof-port scalar choices with `uint32_t` for `portTickType` and `int` for
`portBASE_TYPE`.  Runtime ABI gates require both to be exactly 32 bits.  Every
JSONL run records the host `unsigned long` width and this adapter explicitly.

This adapter supplies types and port macros only.  It does not alter kernel
state after an upstream operation.  The named critical/yield contract bodies
are included unchanged and their three observables are present in every
snapshot.

## Required scenarios

| Scenario | Source step and discriminator |
|---|---|
| normal tick, no wake | `5 -> 6`; wake key `7` stays in the current delayed list; `pxCurrentTCB` is unchanged |
| tick wakes delayed task | `9 -> 10`; expired high-priority TCB moves from delayed to `ready[3]`; tick itself does not switch, a later `vTaskSwitchContext` does |
| tick wrap | real `UINT32_MAX -> 0`; old current delayed list must be empty; physical delayed-list pointers exchange roles; key `1` remains blocked at tick `0` and wakes at tick `1` |
| same-priority FIFO | ready tasks are inserted `A,B,C`; successive source context switches select `A,B,C,A` while preserving ring order |
| positive delay, no wrap | at tick `5`, delaying the current priority-2 task by `2` moves it from ready to current-delayed with key `7`, leaves an idle witness ready, and requests one yield |
| positive delay, wrap | at tick `UINT32_MAX-1`, delaying by `3` gives key `1` in overflow-delayed without swapping the two physical delayed-list roles |

The FIFO setup exposes a non-obvious V6.1.1 detail: `vListInsertEnd` assigns
`pxIndex` to every newly inserted item.  After inserting `A,B,C`, the cursor is
`C`, so the first context switch advances through the sentinel and selects
`A`.  The upstream `prvAddTaskToReadyQueue(pxTCB)` macro also leaves its
parameter unparenthesised; the harness binds a simple local `tskTCB *` before
invoking it rather than changing the macro.

## JSONL observation and rejection gates

Every snapshot records:

- tick, current TCB, top-ready priority, suspension/missed-tick/yield/overflow
  globals;
- physical delayed-list roles and proof-port contract counters;
- all four ready lists, both physical delayed lists, pending-ready and
  suspended lists;
- for every list: count, cursor, ordered ring, keys, item kind, predecessor and
  successor;
- for every synthetic TCB: priority, current flag, generic key, generic
  container, and event-item container.

Before a snapshot is printed, fail-closed checks enforce:

- exact count versus finite traversal;
- two-way next/previous links, exact last node, and cursor in ring-or-sentinel;
- item owner and container agreement;
- no generic/event item occurs in more than one scheduler list;
- container non-NULL iff the item occurs once in the observed list universe;
- ready-list priority agreement and nondecreasing delayed wake keys;
- distinct current/overflow roles over the two physical delayed lists;
- a known current TCB and a quiescent port boundary;
- at `StableRunning`, an exact highest-nonempty ready cache and a current TCB
  in its ready list;
- at `YieldPending`, an upper-bound (possibly stale) ready cache, a current TCB
  in a delayed role, and a positive proof-port yield ledger.

The phase split is load-bearing.  Immediately after positive `vTaskDelay`,
the source has blocked the selected TCB but the proof port has only recorded a
yield request; it has not performed a context switch.  At that boundary,
"current is ready" and "the top-ready cache is exact" are both false, while
the weaker phase-indexed obligations remain true.

Scenario-specific checks reject plausible but false invariants, including
"tick directly switches to a newly readied task", "wrap moves nodes rather
than swapping list roles", and "same-priority selection ignores the list
cursor".

## Explicit stub policy

The full upstream translation unit contains task-creation, heap, and scheduler
start/end paths outside these scenarios.  Link closure supplies seven named
stubs:

```text
pxPortInitialiseStack  pvPortMalloc        vPortFree
vPortInitialiseBlocks xPortGetFreeHeapSize
xPortStartScheduler   vPortEndScheduler
```

If any is reached it emits a `stub_reached` JSON record and terminates.  No
stub returns fabricated memory, stack state, or a successful scheduler result.
The runner rejects any `stub_reached` or `invariant_failure` record.

## Reproduction

```powershell
./scripts/run-scheduler-trace.ps1 `
  -RunId 20260731Tscheduler-trace-03-delay-phases `
  -TimeoutSeconds 60
```

The runner uses bounded WSL GCC with C99, `-Wall -Wextra -Werror`, and
`-fno-strict-aliasing`, parses every JSONL record, requires all six scenarios
and the final success gate, and records hashes for the harness, runner, proof
port inputs, upstream sources, binary, trace, and analysis.

The extended run completed in 6.097 s with compile/trace/analysis exit codes
`0/0/0`, 57 JSONL records, 17 snapshots, 39 successful checks, all six
required scenarios, and zero fatal records.  Its harness/runner/binary/trace/
analysis SHA-256 values are respectively
`9B9BD5D73AFBBCB7715016A8A1A1D9A2FF8A14471FBBE31CF2EA70205D5123A7`,
`1D855DF45BBBB009725AED8C203D8FE529D6EEF8EEA5D88F10FF492121C0DD84`,
`D6C9B6480C38165B33D2D57846D9A007E1E0FB0AD53EAF1D2D79A82CE16737FF`,
`125A7B9F605DC41C894EEB39D4AED3A128963FF05A6C1758E7A5CEF45EC099A8`,
and `2E2821F00974776D29BA53A3772F8C975261E78F82FF16A46EB986D3AF2C08BD`.

The earlier `20260731Tscheduler-trace-01` and
`20260731Tscheduler-trace-02-independent` runs remain the byte-for-byte
four-scenario reproducibility pair.  The initial run alone additionally
received a manual `-fsanitize=address,undefined` check; that sanitizer result
is historical and is not claimed for the extended run.
