# Proof-port contract ledger

Status: `LIST_C_SPLIT_HEAP_BLOCKED__RAW_R5_FIXED_INSERT_REFINEMENT_GREEN__SCHEDULER_TRACE_REPRO_GREEN__GENERAL_N_REMOVE_SCHEDULER_REFINEMENT_PENDING`

This directory supplies configuration and port headers needed to preprocess
the unmodified upstream `Source/list.c`.  The headers are an explicit proof
environment contract.  They are not a claim that a particular hardware port
or deployed FreeRTOS configuration has been verified.

## Upstream integrity

- `upstream/FreeRTOSV6.1.1/Source/list.c` remains unmodified.
- Frozen SHA-256: `EEAD2C4F6AEB2DA0CF4A5606EC4A213EF492B09C12DF1A0097B6442688C82ABB`.
- Include order is `proof_port/` followed by the official
  `Source/include/`; the proof port does not shadow `FreeRTOS.h`, `list.h`,
  `portable.h`, `projdefs.h`, or `mpu_wrappers.h`.
- Each custom header in the transitive `list.c` include closure is registered
  with CParser via `include_C_file`. CParser preprocesses a sanitized temporary
  copy and does not implicitly copy the contents of `new_C_include_dir`.

## `FreeRTOSConfig.h`

| Macro | Value | Contract and observable effect |
|---|---:|---|
| `configUSE_PREEMPTION` | 1 | Selects the preemptive scheduler configuration for later work. It does not alter any body in `list.c`; no scheduler theorem follows from this smoke. |
| `configUSE_IDLE_HOOK` | 0 | No idle hook. Required by `FreeRTOS.h`, not executed or inspected by `list.c`. |
| `configUSE_TICK_HOOK` | 0 | No tick hook. Required by `FreeRTOS.h`, not executed or inspected by `list.c`. |
| `configUSE_CO_ROUTINES` | 0 | Co-routines are outside the frozen scheduler slice. No `list.c` body depends on this value. |
| `configUSE_16_BIT_TICKS` | 0 | Load-bearing: `portTickType` is a 32-bit unsigned word in the CParser machine and `portMAX_DELAY` is `2^32-1`. This fixes list ordering and the end-marker value. |
| seven `INCLUDE_*` API switches | 1 | Avoids preprocessing away candidate scheduler APIs in later translation work. These switches do not change `list.c`. The exact scheduler API allowlist remains subject to `SOURCE_SCOPE.md`. |

## `portmacro.h`

| Item | Contract |
|---|---|
| `portBASE_TYPE` | C `long`; 32 bits under the selected CParser machine. Used by the `xList.uxNumberOfItems` declaration. |
| `portSTACK_TYPE` | C `unsigned long`; needed only to type declarations in `portable.h` during this smoke. |
| `portTickType` | C `unsigned long`, hence a 32-bit word in the selected CParser machine. |
| `portMAX_DELAY` | `(portTickType) 0xffffffffUL`; the sentinel value written by `vListInitialise` and treated specially by `vListInsert`. |
| `portBYTE_ALIGNMENT` | 4; selects the corresponding mask in `portable.h`. No `list.c` body reads it. |
| critical/interrupt/yield macros | Empty external-boundary macros. None occurs in the five upstream `list.c` function bodies, so this does not erase an executed list effect. They must be replaced by an audited scheduler-operation contract before translating code that invokes them. |

The contract is satisfiable for the list smoke: it requires ordinary aligned
objects interpreted with the CParser's 32-bit scalar layout and makes no claim
about interrupt interleavings.  Pointer validity, list shape, and aliasing are
future theorem premises, not injected by these headers.

## Heap-lift representation choice

Upstream takes the address of the embedded `xLIST.xListEnd` mini-list sentinel
and casts that common-prefix address to `xListItem *`. AutoCorres2 therefore
requires `addressable_fields = xLIST.xListEnd` before split-heap lifting. This
is the documented open-structure mechanism: the field remains represented in
the common memory heap so the source-level address and alias are retained.
It is not `ignore_addressable_fields_error`, not a source rewrite, and not an
assumption that the alias is absent.

This mechanism preserves the source address but does not make every split
typed-root guard jointly satisfiable.  Checker-green run
`20260731Tm0-bridge-07-operational-top` proves that, when a valid `xLIST_C`
has its cursor at the cast embedded sentinel, the split-heap
`vListInsertEnd'` execution is `top` and has no `runs_to` result.  This blocks
the standard split-heap encoding for the intended empty-list insert path; it
does not show that the untouched C path or the alternative raw-heap semantics
is empty.

## Uncalled port prototypes

Official `portable.h` declares seven hardware/allocation interfaces without
providing bodies in this translation unit:

`pxPortInitialiseStack`, `pvPortMalloc`, `vPortFree`,
`vPortInitialiseBlocks`, `xPortGetFreeHeapSize`, `xPortStartScheduler`, and
`vPortEndScheduler`.

AutoCorres2 is given these names through `no_body`. This creates explicit
external nondeterministic operations, but none is reachable from any of the
five `list.c` functions: their source bodies contain no calls at all. Thus the
stubs cannot affect this list translation smoke. They are not specifications
of allocation, startup, shutdown, interrupts, or scheduling, and a later
translation whose call graph reaches one must replace its stub with a reviewed
contract or implementation.

## Freestanding standard-header surface

The WSL host's glibc headers are not part of the target program or its ABI.
Expanding them produced a 206,465-byte `list.i` containing host-only GNU
extensions and 64-bit declarations that StrictCParser rejected. Two explicit
proof headers therefore define the freestanding surface actually used here:

- `stddef.h`: 32-bit `unsigned long size_t` and the standard null pointer
  macro;
- `stdlib.h`: includes that `stddef.h` and declares nothing else.

This does not suppress an executed library call: none of the five `list.c`
functions calls a standard-library function. `portable.h` uses `size_t` only
in external allocation prototypes whose bodies are absent and never called by
`list.c`. Any later source that calls libc requires a new audited contract.

## Preprocessor bridge provenance

`scripts/cpp-wsl.sh` is copied byte-for-byte from the generic ABAV toolchain
helper at:

`C:\Users\Chengsong\Downloads\abav_staircase_starter\abav_staircase_starter\artifacts\autocorres2\toolchain\cpp-wsl.sh`

Source SHA-256:
`E1BA42D5D3DD658DE01859A874A3C4CDCA7BB4102C1B0E0EC9AEC093EE95C13B`.

The bridge translates Cygwin absolute paths and `-I` paths to WSL paths, then
executes Ubuntu `/usr/bin/cpp`; it does not rewrite C tokens or add macros.
ABAV remained read-only.

The theory records the bridge as an absolute Cygwin path because CParser runs
the configured preprocessor from an Isabelle temporary directory; a path
relative to the theory master directory is therefore not executable there.
This machine-specific location is part of `TOOLCHAIN_LOCK.md`, not a semantic
source substitution.

## Translation-smoke checker evidence

Run `20260731Tlist-smoke-12-final` built session
`EAL6_FreeRTOS_V611_List_Smoke` with Isabelle2025-2 and AFP AutoCorres2,
`quick_and_dirty=false`, exit code 0, and 46.829 s elapsed time.  The durable
run record is `runs/20260731Tlist-smoke-12-final/status.txt`; its stdout and
stderr SHA-256 values are respectively
`F2F76D8CC7CF6BE4DABA28174AA135AC47C16B5CE2866FBFAFA12304F2369CD9`
and `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6`.
The actual session database is in the default Isabelle store documented in
`TOOLCHAIN_LOCK.md`; the stale requested-store line in this early status file
is corrected by failure entry F-0013.

The exported PIDE message stream is 794,983 bytes with SHA-256
`BF9FE410D4750191ED37B5C1F4051762ECD9544CE1387456A8E88FBBA404996D`.
It records CParser translation and every AutoCorres phase for all five upstream
function bodies.  The generated constants have these checker-reported types:

- `vListInitialise' :: xLIST_C ptr \<Rightarrow> (unit, unit, lifted_globals) spec_monad`;
- `vListInitialiseItem' :: xLIST_ITEM_C ptr \<Rightarrow> (unit, unit, lifted_globals) spec_monad`;
- `vListInsertEnd' :: xLIST_C ptr \<Rightarrow> xLIST_ITEM_C ptr \<Rightarrow> (unit, unit, lifted_globals) spec_monad`;
- `vListInsert' :: xLIST_C ptr \<Rightarrow> xLIST_ITEM_C ptr \<Rightarrow> (unit, unit, lifted_globals) spec_monad`;
- `vListRemove' :: xLIST_ITEM_C ptr \<Rightarrow> (unit, unit, lifted_globals) spec_monad`.

This green result is deliberately classified as a translation smoke, not a
refinement theorem.  The PIDE stream contains two load-bearing heap-lift
warnings: `field_lvalue` could not be removed from `vListInitialise` and
`vListInsert`, so their generated programs may be unprovable until the
embedded-sentinel alias is handled in the representation relation.  It also
reports `unchanged_typing` proof failures for each of the seven `no_body` port
operations listed above.  Those operations are unreachable from the five list
bodies, so the warnings do not invalidate this translation smoke; they remain
explicit blockers for any later proof whose call graph reaches a port stub.

## Raw-heap operational staircase (not refinement)

The official `skip_heap_abs` translation of the same untouched `list.c` is
checker-green in `20260731Tlist-raw-skip-01`.  Its definitions retain raw
`hrs_mem`/`h_val` updates and `c_guard` checks instead of the incompatible
split typed roots.  The following theorem staircase is named `Raw-R*` to avoid
collision with the R0/R1/R2 representation alternatives in
`DESIGN_LEDGER.md`:

| Rung | Final checker evidence | Scope |
|---|---|---|
| `Raw-R0` | `20260731Tlist-raw-r0-05-guards`, 21.774 s, `quick_and_dirty=false` | Fixed-address `c_guard` witnesses for the list, detached item, and cast sentinel. |
| `Raw-R1` | `20260731Tlist-raw-r1-05-init`, 23.832 s, `quick_and_dirty=false` | Positive `vListInitialise'` result, exact empty-list fields, and one byte-frame theorem. |
| `Raw-R2` | `20260731Tlist-raw-r2-04-init-item`, 22.001 s, `quick_and_dirty=false` | Positive `vListInitialiseItem'` result with exact container update and item/list/byte frames. |
| `Raw-R3a` | `20260731Tlist-raw-r3a-01-prefix`, 29.643 s, `quick_and_dirty=false` | Cast-sentinel/common-prefix key and link projections on arbitrary raw heaps. |
| `Raw-R3b` | `20260731Tlist-raw-r3b-19-selector-frames`, 22.432 s, `quick_and_dirty=false` | Embedded-list update normalization, selector frames, and preservation of the eight trailing bytes. |
| `Raw-R3c` | `20260731Tlist-raw-r3c-06-prestate`, 22.666 s, `quick_and_dirty=false` | Exact empty-list/fresh-item raw witness with ten projected fields and unchanged heap typing. |
| `Raw-R3d` | `20260731Tlist-raw-r3d-05-result`, 24.132 s, `quick_and_dirty=false` | Positive source-derived raw `vListInsertEnd'` result at the exact witness. |
| `Raw-R3e` | `20260731Tlist-raw-r3e-04-count-index-post`, 75.863 s, `quick_and_dirty=false` | Result, count 1, and cursor at the inserted item. |
| `Raw-R3f` | `20260731Tlist-raw-r3f-09-container`, 25.860 s, `quick_and_dirty=false` | Exact sentinel links, item links, and item container postconditions. |
| `Raw-R3g` | `20260731Tlist-raw-r3g-10-canary-htd`, 24.313 s, `quick_and_dirty=false` | Key/owner, tail8, far-canary, and heap-typing frame groups. |
| `Raw-R3-master` | `20260731Tlist-raw-r3-master-01`, 33.513 s, `quick_and_dirty=false` | One exact empty-to-singleton insert theorem mechanically conjoining all eight postcondition groups. |

These operational results establish a concrete raw construction plus the exact
empty-to-singleton `vListInsertEnd'` segment.  Each remains classified as
non-refinement; none is relabelled after the later semantic bridge.

## Fixed raw-heap-to-abstract simulation

The separate `Raw-R5` rung is the first source-to-abstract result.  Run
`20260731Tlist-raw-r5-10-show-thesis` checks session
`EAL6_FreeRTOS_V611_List_Raw_R5_Relation` in 25.236 s with exit 0,
`quick_and_dirty=false`, and no timeout.  Theory
`List_V611_Raw_R5_Relation.thy` has SHA-256
`5CD5EF0B3850FEBD712664EA375ED04E3BDDD2C8B80B9AEA75EBDF006613A199`.

The theory defines the raw list observation functions and `raw_xlist_rel`,
then checks only its empty and singleton constructor fragment.
`raw_insert_end_prestate_rep_empty` supplies the related concrete prestate;
`raw_vListInsertEnd_empty_refines` maps the positive source-derived raw
`vListInsertEnd'` result to independently defined `list_insert_end_abs`.  This
fixed empty-to-singleton theorem raises the refinement count to one, but does
not establish general-N representation, `vListRemove'`, ordered insertion, the
sequential full needle, or any scheduler refinement.

## Scheduler proof-port preparation (not checker-green)

The list smoke's headers remain unchanged.  Scheduler translation uses the
isolated `proof_port/scheduler/` include directory and the composition unit
documented in `SCHEDULER_TRANSLATION_PREP.md`.

Reachable critical-section and yield macros now expand to named C contract
bodies with observable depth, interrupt-state, and yield-count effects.  They
are not empty macros and are not bodyless externals.  The intended abstraction
is an atomic sequential API call ending in a recorded yield request; a future
port-refinement theorem must connect that contract to real interrupt and
context-switch behaviour.

The combined unit places `tasks.c` before `list.c` so the upstream
`MPU_WRAPPERS_INCLUDED_FROM_API_FILE` include discipline is preserved.  No
upstream source body is copied or rewritten.

## Scheduler executable trace contract (not refinement)

The executable harness uses the same load-bearing composition order: the
unchanged named scheduler port-contract body, untouched upstream `tasks.c`,
then untouched upstream `list.c`, all in one C translation unit.  This permits
read-only observation of scheduler file-static state without removing
`static`, adding source hooks, or copying an upstream operation body.  Each
snapshot records the port contract's critical-depth, interrupt-state, and
yield-count observables; all scenario boundaries require them to be
quiescent.

There is one explicit host-only ABI adapter.  The proof port is intended for a
32-bit StrictCParser machine where its C `long`-based scalar choices are 32
bits, while WSL GCC is LP64.  The harness therefore spells the proof-equivalent
tick/base scalars as `uint32_t`/`int` and rejects the run unless both are
exactly 32 bits.  This preserves real `UINT32_MAX -> 0` execution and is an
audited harness boundary, not a stub for scheduler state.

Seven out-of-scope link-closure functions are fail-closed:
`pxPortInitialiseStack`, `pvPortMalloc`, `vPortFree`,
`vPortInitialiseBlocks`, `xPortGetFreeHeapSize`, `xPortStartScheduler`, and
`vPortEndScheduler`.  Reaching any one emits `stub_reached` and terminates; no
stub returns fabricated memory or state.  The final independent run reached
none of them and recorded no invariant failure.

Run `20260731Tscheduler-trace-02-independent` is the final reproducibility
evidence.  It completed in 5.621 s with bounded compile/trace/analysis exit
codes `0/0/0`, 39 records, 13 full snapshots, 25 successful checks, all four
required scenarios, and zero fatal records.  Its status ledger records
byte-identical harness, runner, proof-port, upstream-source, binary, trace,
and analysis hashes relative to `20260731Tscheduler-trace-01`; the binary,
trace, and analysis hashes are respectively
`98FCD95AF034F7CF7908A0D47345CF1CD0682D87578C4FF9D2836E07086FEEB2`,
`A8BB9ED04B32D98186FCE87FFDB2E5C9885A97CFE3B68AB306F76E3699B46C67`,
and `DF1B92DA3B23FAE0B5FDAB94503FB51F9DE86F4838049AEC5D7DBD59A9F98385`.

Only the initial run additionally received a separate manual
ASan/UBSan compile-and-run check (`0/0`, no reported sanitizer error).  That
sanitizer claim does not attach to the independent rerun.  These results test
the executable proof-port boundary and generate scheduler invariant
candidates; they are neither an Isabelle checker result nor a
source-to-abstract scheduler refinement theorem.

## Conditional positive-delay P2 source refinement (2026-08-01)

The real generated `vTaskDelay' 2` path is now checker-green through three
separate layers:

1. `Scheduler_P2_Delay_Source` composes exact suspend, remove, generated
   wake-key write, delayed-A insertion, quiet resume, and yield states;
2. `Scheduler_P2_Post_Relation` proves the final relation for all eight
   physical list roots, including both root and P2_IDLE item framing for the
   nonempty ready0 list;
3. `Scheduler_P2_Delay_Refinement` proves the remaining endpoint fields and
   relates the real source result to `task_delay_abs 2 p2_pre`.

The final runs were respectively
`20260801Tscheduler-p2-delay-source-09-canonical-states` (35.056 s),
`20260801Tscheduler-p2-post-relation-09-nat-index` (38.618 s), and
`20260801Tscheduler-p2-delay-refinement-04-final-heap` (39.603 s), all exit 0
with `quick_and_dirty=false`.  Their theory hashes are respectively
`7BFB623FE099104EA4276D0119CCD6C7B23A0F94ABF04B87FAAFAF3AEB1DD6C0`,
`CF5CCB728150BC4B185CEAE448E9E2FAB0C9C88E1CCBCDA1F79E2A67AD7375B8`,
and `43BC41254C609DF8302F38113F662912E2FD99C72D0A612E5A72925E5AA1C9E7`.

This raises the conditional source-to-abstract theorem count to twelve.  It is
not yet a deployment-instance theorem: the addressed scheduler data globals
still need a checked layout certificate and concrete P2 preimage for one
frozen ELF.  AutoCorres2 already supplies symbolic execution and VCG; SMT or a
second executor would not provide those missing linker-layout facts.
