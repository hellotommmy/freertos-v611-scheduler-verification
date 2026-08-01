# Scheduler translation preparation ledger

Status: `STATIC_C_SYNTAX_GREEN__ISABELLE_UNCHECKED`

This ledger covers the five frozen scheduler roots plus
`vTaskSuspendAll`/`xTaskResumeAll`.  It is an independent source audit.  No
original formalisation or proof artifact was consulted.

## Composition and provenance

`proof_port/scheduler/scheduler_translation_unit.c` includes, in this order:

1. the named sequential proof-port contract;
2. the unmodified upstream `Source/tasks.c`;
3. the unmodified upstream `Source/list.c`.

Putting `tasks.c` before `list.c` is load-bearing.  `tasks.c` defines
`MPU_WRAPPERS_INCLUDED_FROM_API_FILE` before its first FreeRTOS include.  If
`list.c` includes `FreeRTOS.h` first, the include guards preserve the wrong MPU
API remapping when `tasks.c` is subsequently read.  The corrected order changes
no upstream token.

The wrapper is a composition device, not part of the 670-line semantic target.
The frozen source archive and per-file hashes remain those in
`upstream/SHA256SUMS`.

## Configuration-active effects

The scheduler-specific `FreeRTOSConfig.h` fixes four priorities, 32-bit ticks,
both delay APIs, and the same seven enabled `INCLUDE_*` switches used by the
list smoke.  The following source features are explicitly inactive:

- trace hooks and trace-buffer writes;
- runtime-statistics reads and TCB fields;
- both stack-overflow check macros;
- the application tick hook;
- mutex, application-tag, and MPU fields.

`portUSING_MPU_WRAPPERS` must be absent before `mpu_wrappers.h` is read.  That
header tests presence, not numeric truth: defining it as `0` still selects the
MPU/section-attribute branch.  Its non-MPU fallback then defines the observable
post-include value `0` and empty `PRIVILEGED_FUNCTION`/`PRIVILEGED_DATA` macros.

The four-priority value is a concrete proof environment choice, not a claim
about every deployment.  The later abstract refinement must either expose the
priority bound as a parameter or state this instantiation in its theorem.

## Exact operational closure

| Root/body | Configuration-active callable bodies and effects |
|---|---|
| `xTaskGetTickCount` | `eal6_port_enter_critical`, read `xTickCount`, `eal6_port_exit_critical` |
| `vTaskDelay` | `vTaskSuspendAll`; for nonzero delay, `vListRemove` and `vListInsert`; `xTaskResumeAll`; possibly `eal6_port_yield` |
| `vTaskDelayUntil` | same closure as `vTaskDelay`, plus the unconditional modular update of `*pxPreviousWakeTime` |
| `vTaskIncrementTick` | either increment `uxMissedTicks`, or increment `xTickCount`, swap delayed-list roles on wrap, and use `vListRemove`/`vListInsertEnd` to wake expired tasks |
| `vTaskSwitchContext` | no C call after configuration expansion; it either sets `xMissedYield` or walks the ready-list macros, advances the selected cursor, and changes `pxCurrentTCB` |
| `vTaskSuspendAll` | increment `uxSchedulerSuspended` |
| `xTaskResumeAll` | critical enter/exit; decrement suspension; drain the pending-ready list through `vListRemove`/`vListInsertEnd`; replay missed ticks through `vTaskIncrementTick`; possibly `eal6_port_yield` |

The list macros are inline source effects.  All five stock list bodies are in
the combined translation unit; none is replaced by `no_body`.

Important theorem preconditions exposed by this audit are:

- `xTaskResumeAll` starts with `uxSchedulerSuspended > 0` (otherwise the
  unsigned decrement underflows);
- suspension and proof-port nesting counters do not wrap;
- `pxCurrentTCB` and its generic list item are valid whenever a delay is taken;
- current/overflow delayed lists are distinct well-formed lists with the roles
  selected by `xTickCount`;
- `uxTopReadyPriority < 4`, and a nonempty ready list exists at or below it, so
  `vTaskSwitchContext` cannot underflow its search;
- every list owner reached by scheduler macros is a valid TCB with a priority
  below four.

## Named port contract and atomicity boundary

Reachable critical and yield macros are not erased:

- enter increments `eal6_port_critical_depth` and sets
  `eal6_port_interrupts_disabled`;
- exit conditionally decrements the depth and clears the interrupt flag only
  when the depth reaches zero;
- yield increments `eal6_port_yield_count` without directly changing the
  kernel's current-task pointer;
- interrupt disable/enable and ISR-mask helpers also have named C bodies, but
  are outside the frozen root closure.

This is a sequential API-boundary model.  A source theorem therefore describes
the kernel state at the API boundary plus a yield request.  It assumes no
unmodelled ISR step is interleaved inside a protected region and does not claim
that incrementing the yield counter is a hardware context switch.  Deployment
refinement needs a separate port theorem relating these three observables to
interrupt masking, nesting, and the eventual scheduler transition.

## External-body reachability audit

The final explicit AutoCorres scopes contain every callable body in the table
above.  Hence the frozen roots reach **zero bodyless external functions**.

The whole parsed translation unit still contains unscoped helpers that call
`pxPortInitialiseStack`, `pvPortMalloc`, `vPortFree`, `xPortStartScheduler`,
`vPortEndScheduler`, `strncpy`, and `memset`; `vPortInitialiseBlocks` and
`xPortGetFreeHeapSize` are also declared.  They are not named in a scheduler
scope and are not silently used as proof contracts.  Any future scope expansion
that reaches one must add a reviewed implementation/specification or an
explicit `no_body` entry and then fail the refinement gate until its contract is
discharged.

This explicit-scope rule matters because AutoCorres2 otherwise translates a
selected function's omitted direct callee through a trivial SIMPL wrapper.
The staircase scopes therefore enumerate the port bodies, list bodies, and
internal scheduler closure rather than relying on wrapper generation.

## Staircase and static gates

Prepared sessions, each in an exclusive theory directory:

1. `EAL6_FreeRTOS_V611_Scheduler_Parse` -- CParser only;
2. `EAL6_FreeRTOS_V611_Scheduler_Tick` -- `xTaskGetTickCount` and both critical
   contract bodies;
3. `EAL6_FreeRTOS_V611_Scheduler_Delay` -- `vTaskDelay`, internal resume/tick
   closure, yield contract, and all five list bodies;
4. `EAL6_FreeRTOS_V611_Scheduler_Roots` -- `vTaskDelayUntil` and
   `vTaskSwitchContext`, completing the five frozen roots.

No Isabelle session in this staircase has run yet.  A WSL GCC C99 syntax-only
pass over the exact composition succeeds.  This is only a preprocessing/type
oracle: WSL GCC uses a host ABI and cannot replace the 32-bit StrictCParser and
AutoCorres gates.

The earlier unsliced parser-footprint estimate remains
5,603 physical / 4,660 nonblank / 2,274 nonblank-noncomment lines.  A direct
raw-file union for the prepared wrapper's actual dependency list is
5,575 / 4,639 / 2,354 under the repository masking rule; proof-port contract
files explain the changed third count.  The `cpp -P` generated unit is 924
lines.  These parser/tool figures are reported separately and never replace
the frozen upstream semantic slice of 670 / 587 / 458.

## Unchecked risks for the first build

- StrictCParser may require a syntax adjustment despite the GCC oracle.
- AutoCorres may require TCB list-item fields to be declared addressable in
  addition to the already checked `xLIST.xListEnd` sentinel.
- global arrays, volatile scheduler globals, and the pending-ready/tick loop
  can force a less abstract monad than the current `ts_rules = nondet` request;
- an incremental scope may expose an omitted callee despite the static audit;
  any such wrapper is a closure bug to fix, not a proof assumption.
