# Scheduler generated layout probe for `raw_scheduler_rel`

Status: `CHECKER_GREEN_LAYOUT_FIRST__CROSS_PARSER_STRUCT_UNIVERSES_DISTINCT__NO_FOOTPRINT_THEOREM__NO_ORIGINAL_FORMALISATION`

The initial static part of this note records only names and terms found in the
frozen FreeRTOS V6.1.1 source, the current CParser/AutoCorres theories, or
their already-built PIDE exports.  The final sections now record a new,
bounded checker run of the minimal layout-first leaf.  Its result was read
back with `isabelle export -n`; `-n` forbids an export-time session build.  No
proof search or original formalisation was opened for this probe.

## Evidence boundary

The main evidence was:

| Evidence | SHA-256 |
|---|---|
| `upstream/FreeRTOSV6.1.1/Source/tasks.c` | `0A5B6C12AEA6FAE2A951C0E80BDC301C646EF8C6360D574A2C4699D4C33A45BF` |
| `proof_port/scheduler/scheduler_port_contract.c` | `A99353238F40F2A987AC15DD1E8E6F95BDAC4CF177A16BBBEE7FD5D145FFBD38` |
| `theories/scheduler_parse/Scheduler_V611_Parse.thy` | `353A991C993A16F33D197E51709D39958DA8F64672AC82D1E14CBDDB127BBF09` |
| `theories/scheduler_delay/Scheduler_V611_Delay_Translation.thy` | `D34512E4642779C49BF412E7FF05E4FB622EF47E255F152AA1CB765E7EA89A68` |
| `theories/scheduler_roots/Scheduler_V611_Roots_Translation.thy` | `B560345AB2B38ADC871060A33E7A850E8603C8CC5DADFD6D1945A2FD2C3A3E7B` |
| Parse `PIDE/messages` export | `EED744A2876D23104EBEDAC5FE244AC516FF876E7CCAD9B2E1D98577D33E8763` |
| Parse `theory/consts` export | `E6DF1F44DF5619F68465A4197B31E1073FD82BB08DDB9A9F4779D35334F6BA99` |
| Parse `theory/thms` export | `12B791477FB4BCEBCB2A7783B3C302E72C988D2995D72434612F1BE4508B56AA` |
| Delay `PIDE/messages` export | `8EA3890C8603AD7EE57746ABC79251662DEA618A9F03D6A75BC7DC52B64437B7` |
| Roots `PIDE/messages` export | `C8CE12231A2C466D33A11FF9D86F28A6EA74A7E6809C2B04E7FD764CE9E4EA88` |

The parse message says there are 23 C globals, of which exactly six are
addressed variables:

```text
pxReadyTasksLists, xDelayedTaskList1, xDelayedTaskList2,
xPendingReadyList, xSuspendedTaskList, xTasksWaitingTermination
```

Consequently, the list objects below are heap-resident addressed globals, not
fields selected from a `globals` value.  The remaining relevant scheduler and
proof-port variables are fields of the generated `globals` record.

## Exact confirmed: TCB fields and terms

The parse `PIDE/messages` export prints the following selector types, and
`theory/consts` contains the corresponding fully qualified entities under
`Scheduler_V611_Parse.tskTaskControlBlock_C`:

```isabelle
xGenericListItem_C :: tskTaskControlBlock_C \<Rightarrow> xLIST_ITEM_C
xEventListItem_C   :: tskTaskControlBlock_C \<Rightarrow> xLIST_ITEM_C
uxPriority_C       :: tskTaskControlBlock_C \<Rightarrow> 32 word
```

The exact heap reads needed by a decoder are therefore:

```isabelle
xGenericListItem_C (h_val (hrs_mem (t_hrs_' c)) tp)
xEventListItem_C   (h_val (hrs_mem (t_hrs_' c)) tp)
uxPriority_C       (h_val (hrs_mem (t_hrs_' c)) tp)
```

The generated `vTaskDelay'_def`, `vTaskDelayUntil'_def`,
`xTaskResumeAll'_def`, and `vTaskIncrementTick'_def` print these exact embedded
item address terms:

```isabelle
PTR(xLIST_ITEM_C) &(tp\<rightarrow>[''xGenericListItem_C''])
PTR(xLIST_ITEM_C) &(tp\<rightarrow>[''xEventListItem_C''])
```

The positive-delay key write additionally uses the exact nested field term:

```isabelle
PTR(32 word) &(tp\<rightarrow>[''xGenericListItem_C'', ''xItemValue_C''])
```

Do not replace the two item addresses by an owner-based decoder: both embedded
items have the same TCB owner.  Their field paths distinguish `Generic` from
`Event`.

The parse `theory/thms` export confirms these exact generated field-layout fact
names:

```text
tskTaskControlBlock_C_xGenericListItem_C_fl
tskTaskControlBlock_C_xGenericListItem_C_fl_Some
tskTaskControlBlock_C_xGenericListItem_C_fl_ti
tskTaskControlBlock_C_xEventListItem_C_fl
tskTaskControlBlock_C_xEventListItem_C_fl_Some
tskTaskControlBlock_C_xEventListItem_C_fl_ti
tskTaskControlBlock_C_uxPriority_C_fl
tskTaskControlBlock_C_uxPriority_C_fl_Some
tskTaskControlBlock_C_uxPriority_C_fl_ti
```

The short `_fl` facts are the form already used with `field_lvalue_def` by the
raw-list theories.  Their concrete statements and numeric offsets were not
printed by the existing scheduler theories, so those details remain in the
unresolved section below.

## Exact confirmed: the eight physical scheduler list roots

There are no generated constants such as `ready0` or
`pxReadyTasksLists_0'`.  The generated ready-list term is an indexed element of
one addressed array base.  Both `xTaskResumeAll'_def` and
`vTaskSwitchContext'_def` print this exact schema:

```isabelle
array_ptr_index pxReadyTasksLists_' False
  (unat (uxPriority_C (h_val (hrs_mem (t_hrs_' c)) tp)))
```

For an abstract priority `p :: nat`, the corresponding root term is therefore
the same generated schema with the already-natural index:

```isabelle
array_ptr_index pxReadyTasksLists_' False p
```

The eight physical roots for the configured `configMAX_PRIORITIES = 4` are:

| Abstract physical root | Exact generated term |
|---|---|
| ready priority 0 | `array_ptr_index pxReadyTasksLists_' False 0` |
| ready priority 1 | `array_ptr_index pxReadyTasksLists_' False 1` |
| ready priority 2 | `array_ptr_index pxReadyTasksLists_' False 2` |
| ready priority 3 | `array_ptr_index pxReadyTasksLists_' False 3` |
| delayed physical A | `xDelayedTaskList1_'` |
| delayed physical B | `xDelayedTaskList2_'` |
| pending-ready | `xPendingReadyList_'` |
| suspended | `xSuspendedTaskList_'` |

`theory/consts` confirms all five base/object constant entities, fully
qualified as follows:

```text
Scheduler_V611_Parse.pxReadyTasksLists_'
Scheduler_V611_Parse.xDelayedTaskList1_'
Scheduler_V611_Parse.xDelayedTaskList2_'
Scheduler_V611_Parse.xPendingReadyList_'
Scheduler_V611_Parse.xSuspendedTaskList_'
```

The generated bodies use the unqualified forms shown in the table.  In
particular, do not write `xDelayedTaskList1_' c`: it is an address constant,
not a state selector.

`vTaskSwitchContext'_def` also confirms that both of these guards occur for a
ready access:

```isabelle
c_guard pxReadyTasksLists_'
c_guard (array_ptr_index pxReadyTasksLists_' False p)
```

The parse theorem export confirms the exact locale/fact entities
`scheduler_translation_unit_global_addresses_def`,
`scheduler_translation_unit_global_addresses.intro`, and
`scheduler_translation_unit_global_addresses.all_distinct`.  The final fact is
the first candidate for discharging physical-global separation, subject to
printing its statement.

## Exact confirmed: state selectors for the relation

The parse message prints the generated record field types.  The existing
checker-green scheduler refinement theories independently use the short
selector spellings below.

| Relation component | Exact selector term | Generated value type |
|---|---|---|
| current TCB | `pxCurrentTCB_' c` | `tskTaskControlBlock_C ptr` |
| semantic current-delayed role pointer | `pxDelayedTaskList_' c` | `xLIST_C ptr` |
| semantic overflow-delayed role pointer | `pxOverflowDelayedTaskList_' c` | `xLIST_C ptr` |
| committed tick | `xTickCount_' c` | `32 word` |
| scheduler suspension depth | `uxSchedulerSuspended_' c` | `32 word` |
| cached top-ready priority | `uxTopReadyPriority_' c` | `32 word` |
| deferred ticks | `uxMissedTicks_' c` | `32 word` |
| deferred yield flag | `xMissedYield_' c` | `32 signed word` |
| tick overflow count | `xNumOfOverflows_' c` | `32 signed word` |
| current task count | `uxCurrentNumberOfTasks_' c` | `32 word` |
| scheduler-running flag | `xSchedulerRunning_' c` | `32 signed word` |
| proof-port yield count | `eal6_port_yield_count_' c` | `32 word` |
| proof-port critical depth | `eal6_port_critical_depth_' c` | `32 word` |
| proof-port interrupt-disabled flag | `eal6_port_interrupts_disabled_' c` | `32 word` |
| raw heap state | `t_hrs_' c` | use through `hrs_mem (t_hrs_' c)` |

The proof-port yield selector is thus exactly
`eal6_port_yield_count_'`, not a kernel `xYield*` field.  The exported
`eal6_port_yield'_def` is exactly:

```isabelle
eal6_port_yield' \<equiv>
  modify (eal6_port_yield_count_'_update (\<lambda>a. a + 1))
```

Three conversion cautions are already fixed by the generated types:

* keep `xTickCount_' c = sa_tick a` as a `32 word` equality;
* use `unat` when the unsigned priority/suspend/missed-tick/top-ready/task/yield
  fields are related to abstract `nat` fields;
* do not use `unat` for `xMissedYield_'`, `xNumOfOverflows_'`, or
  `xSchedulerRunning_'`; all three are `32 signed word` fields.

The role-pointer equations in `raw_scheduler_rel` should compare
`pxDelayedTaskList_' c` and `pxOverflowDelayedTaskList_' c` against the direct
physical constants `xDelayedTaskList1_'` and `xDelayedTaskList2_'`.  The two
kinds of generated name must not be conflated.

## Pre-build unresolved list

The following were deliberately not guessed from naming conventions.  Their
post-build disposition is recorded below; items still open remain explicitly
labelled unresolved.

1. The standalone pretty-printed types of the five addressed-global constants
   and the exact locale context, if any, attached to their useful facts.  Their
   uses force `xLIST_C ptr`-compatible terms, but a first `term` check should
   record the declaration output rather than relying on that inference.
2. The concrete statements and numeric offsets in the three TCB `_fl` facts,
   and the generated numeric `tskTaskControlBlock_C_size`/alignment facts.
3. Whether `scheduler_translation_unit_global_addresses.all_distinct` directly
   yields all full object/array interval separations needed for the eight roots,
   or whether an array-element interval lemma must be added for the four ready
   elements.
4. The exact theorem route from a guarded full TCB to containment of each
   embedded `xLIST_ITEM_C` region and disjointness of the generic/event regions.
   The selector names and field paths are confirmed; this footprint theorem is
   not.
5. The exact forward `tskTaskControlBlock_C ptr` to `unit ptr` coercion to use
   in the two `pvOwner_C` equations.  The generated resume body confirms the
   reverse readback cast
   `PTR_COERCE(unit \<rightarrow> tskTaskControlBlock_C)`, but the forward owner
   equation should be term-checked before it is frozen.

None of these unresolved items blocks writing the syntactic decoder/root
definitions.  They do block claiming the root/TCB footprint and owner clauses
are checker-green.

## Minimal first decoder/root theory statement list (pre-build candidate)

The pre-build candidate imported the scheduler roots translation and only
probed declarations/statements before defining `raw_scheduler_rel`.  The
implemented leaf below additionally imports the independent raw-list relation
to diagnose whether its generated types can be reused directly.

```isabelle
theory Scheduler_P2_Generated_Layout_First
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Roots.Scheduler_V611_Roots_Translation"
begin

(* Exact selector types. *)
term "xGenericListItem_C"
term "xEventListItem_C"
term "uxPriority_C"

(* Exact embedded addresses and heap read. *)
term "(\<lambda>tp :: tskTaskControlBlock_C ptr.
  PTR(xLIST_ITEM_C) &(tp\<rightarrow>[''xGenericListItem_C'']))"
term "(\<lambda>tp :: tskTaskControlBlock_C ptr.
  PTR(xLIST_ITEM_C) &(tp\<rightarrow>[''xEventListItem_C'']))"
term "(\<lambda>(c :: globals) (tp :: tskTaskControlBlock_C ptr).
  uxPriority_C (h_val (hrs_mem (t_hrs_' c)) tp))"

(* Only the short field-layout facts are needed on the first pass. *)
print_statement tskTaskControlBlock_C_xGenericListItem_C_fl
print_statement tskTaskControlBlock_C_xEventListItem_C_fl
print_statement tskTaskControlBlock_C_uxPriority_C_fl
print_statement tskTaskControlBlock_C_size

(* Addressed roots and ready element constructor. *)
term "pxReadyTasksLists_'"
term "(\<lambda>p :: nat. array_ptr_index pxReadyTasksLists_' False p)"
term "xDelayedTaskList1_'"
term "xDelayedTaskList2_'"
term "xPendingReadyList_'"
term "xSuspendedTaskList_'"
print_locale scheduler_translation_unit_global_addresses
print_statement scheduler_translation_unit_global_addresses.all_distinct

(* State/role selectors and proof-port observables. *)
term "(\<lambda>c :: globals.
  (pxDelayedTaskList_' c, pxOverflowDelayedTaskList_' c,
   pxCurrentTCB_' c))"
term "(\<lambda>c :: globals.
  (xTickCount_' c, uxSchedulerSuspended_' c,
   uxTopReadyPriority_' c, uxMissedTicks_' c,
   uxCurrentNumberOfTasks_' c, eal6_port_yield_count_' c,
   eal6_port_critical_depth_' c,
   eal6_port_interrupts_disabled_' c))"
term "(\<lambda>c :: globals.
  (xMissedYield_' c, xNumOfOverflows_' c, xSchedulerRunning_' c))"

(* Source definitions that pin all non-layout spellings used by P2. *)
print_statement vTaskDelay'_def
print_statement xTaskResumeAll'_def
print_statement vTaskIncrementTick'_def
print_statement vTaskSwitchContext'_def

end
```

After these statements are captured, the first actual definitions can safely
use the two confirmed item-address lambdas and
`array_ptr_index pxReadyTasksLists_' False p`.  No further generated root name
should be introduced unless it appears in a checked statement.

## Checker-green implementation

The diagnostic is implemented at
`theories/scheduler_p2_generated_layout_first/Scheduler_P2_Generated_Layout_First.thy`
in session
`EAL6_FreeRTOS_V611_Scheduler_P2_Generated_Layout_First`.  The session is a
child of `EAL6_FreeRTOS_V611_Scheduler_Roots` and registers
`EAL6_FreeRTOS_V611_List_Raw_R5_Relation` as an additional session import.
The theory contains only `term`, `print_locale`, and `print_statement`
diagnostics.  It defines no relation and proves no footprint theorem.

Because the two imported C translations both generate a `globals` record,
the implemented version namespace-qualifies scheduler record selectors as
`Scheduler_V611_Parse.globals.*`.  This is disambiguation only; it does not
invent or rename a generated field.

### Exact field-layout and size output

The final leaf's exported `PIDE/messages` prints:

```isabelle
theorem tskTaskControlBlock_C_xGenericListItem_C_fl:
shows "field_lookup (typ_info_t TYPE(tskTaskControlBlock_C)) [''xGenericListItem_C''] 0 = Some (adjust_ti (typ_info_t TYPE(Scheduler_V611_Parse.xLIST_ITEM_C)) xGenericListItem_C (xGenericListItem_C_update \<circ> (\<lambda>x _. x)), 4)"

theorem tskTaskControlBlock_C_xEventListItem_C_fl:
shows "field_lookup (typ_info_t TYPE(tskTaskControlBlock_C)) [''xEventListItem_C''] 0 = Some (adjust_ti (typ_info_t TYPE(Scheduler_V611_Parse.xLIST_ITEM_C)) xEventListItem_C (xEventListItem_C_update \<circ> (\<lambda>x _. x)), 24)"

theorem tskTaskControlBlock_C_uxPriority_C_fl:
shows "field_lookup (typ_info_t TYPE(tskTaskControlBlock_C)) [''uxPriority_C''] 0 = Some (adjust_ti (typ_info_t TYPE(32 word)) uxPriority_C (uxPriority_C_update \<circ> (\<lambda>x _. x)), 44)"

theorem tskTaskControlBlock_C_size:
shows "size_of TYPE(tskTaskControlBlock_C) \<equiv> 68"
```

Thus the byte offsets are exactly 4, 24, and 44, and the generated TCB size is
exactly 68 bytes.  No alignment fact was probed or inferred.

The same PIDE stream gives the addressed-root types exactly:

```isabelle
"pxReadyTasksLists_'"
:: "(Scheduler_V611_Parse.xLIST_C[4]) ptr"

"array_ptr_index pxReadyTasksLists_' False"
:: "nat \<Rightarrow> Scheduler_V611_Parse.xLIST_C ptr"

"xDelayedTaskList1_'"
:: "Scheduler_V611_Parse.xLIST_C ptr"
"xDelayedTaskList2_'"
:: "Scheduler_V611_Parse.xLIST_C ptr"
"xPendingReadyList_'"
:: "Scheduler_V611_Parse.xLIST_C ptr"
"xSuspendedTaskList_'"
:: "Scheduler_V611_Parse.xLIST_C ptr"
```

### Exact locale and `all_distinct` output

`print_locale scheduler_translation_unit_global_addresses` prints exactly:

```isabelle
locale scheduler_translation_unit_global_addresses
assumes "scheduler_translation_unit_global_addresses"
```

`print_statement scheduler_translation_unit_global_addresses.all_distinct`
prints exactly:

```isabelle
theorem all_distinct:
assumes "scheduler_translation_unit_global_addresses"
shows "all_distinct (Node (Node (Node (Node (Node (Node Tip scheduler_translation_unit.memset False Tip) scheduler_translation_unit.strncpy False (Node Tip scheduler_translation_unit.vPortFree False Tip)) scheduler_translation_unit.vTaskList False (Node (Node Tip scheduler_translation_unit.eal6_port_yield False Tip) scheduler_translation_unit.vListInsert False (Node Tip scheduler_translation_unit.vListRemove False Tip))) scheduler_translation_unit.vTaskSuspendAll False (Node (Node (Node Tip scheduler_translation_unit.eal6_port_enter_critical False Tip) scheduler_translation_unit.eal6_port_exit_critical False (Node Tip scheduler_translation_unit.vListInsertEnd False Tip)) scheduler_translation_unit.vTaskIncrementTick False (Node (Node Tip scheduler_translation_unit.xTaskResumeAll False Tip) scheduler_translation_unit.vTaskDelay False (Node Tip scheduler_translation_unit.prvDeleteTCB False Tip)))) scheduler_translation_unit.prvCheckTasksWaitingTermination False (Node (Node (Node (Node Tip scheduler_translation_unit.prvIdleTask False Tip) scheduler_translation_unit.vTaskDelete False (Node Tip scheduler_translation_unit.xTaskIsTaskSuspended False Tip)) scheduler_translation_unit.vTaskResume False (Node (Node Tip scheduler_translation_unit.init'globals False Tip) scheduler_translation_unit.pvPortMalloc False (Node Tip scheduler_translation_unit.vTaskSwitchContext False Tip))) scheduler_translation_unit.vTaskSuspend False (Node (Node (Node Tip scheduler_translation_unit.ulTaskEndTrace False Tip) scheduler_translation_unit.vListInitialise False (Node Tip scheduler_translation_unit.vTaskDelayUntil False Tip)) scheduler_translation_unit.vTaskStartTrace False (Node (Node Tip scheduler_translation_unit.vTaskMissedYield False Tip) scheduler_translation_unit.vTaskPrioritySet False (Node Tip scheduler_translation_unit.uxTaskPriorityGet False Tip))))) scheduler_translation_unit.vPortEndScheduler False (Node (Node (Node (Node (Node Tip scheduler_translation_unit.eal6_port_disable_interrupts False Tip) scheduler_translation_unit.vTaskEndScheduler False (Node Tip scheduler_translation_unit.xTaskGetTickCount False Tip)) scheduler_translation_unit.prvAllocateTCBAndStack False (Node (Node Tip scheduler_translation_unit.vListInitialiseItem False Tip) scheduler_translation_unit.prvInitialiseTCBVariables False (Node Tip scheduler_translation_unit.prvInitialiseTaskLists False Tip))) scheduler_translation_unit.pxPortInitialiseStack False (Node (Node (Node Tip scheduler_translation_unit.xTaskGenericCreate False Tip) scheduler_translation_unit.xTaskResumeFromISR False (Node Tip scheduler_translation_unit.xPortStartScheduler False Tip)) scheduler_translation_unit.vTaskStartScheduler False (Node (Node Tip scheduler_translation_unit.vTaskGetRunTimeStats False Tip) scheduler_translation_unit.vTaskPriorityInherit False (Node Tip scheduler_translation_unit.vTaskSetTimeOutState False Tip)))) scheduler_translation_unit.xPortGetFreeHeapSize False (Node (Node (Node (Node Tip scheduler_translation_unit.xTaskCheckForTimeOut False Tip) scheduler_translation_unit.vPortInitialiseBlocks False (Node Tip scheduler_translation_unit.vTaskCleanUpResources False Tip)) scheduler_translation_unit.vTaskPlaceOnEventList False (Node (Node Tip scheduler_translation_unit.uxTaskGetNumberOfTasks False Tip) scheduler_translation_unit.xTaskGetSchedulerState False (Node Tip scheduler_translation_unit.vTaskAllocateMPURegions False Tip))) scheduler_translation_unit.vTaskPriorityDisinherit False (Node (Node (Node Tip scheduler_translation_unit.xTaskGetTickCountFromISR False Tip) scheduler_translation_unit.xTaskRemoveFromEventList False (Node Tip scheduler_translation_unit.xTaskGetCurrentTaskHandle False Tip)) scheduler_translation_unit.eal6_port_enable_interrupts False (Node (Node Tip scheduler_translation_unit.uxTaskGetStackHighWaterMark False Tip) scheduler_translation_unit.xTaskCallApplicationTaskHook False (Node Tip scheduler_translation_unit.eal6_port_set_interrupt_mask_from_isr False (Node Tip scheduler_translation_unit.eal6_port_clear_interrupt_mask_from_isr False Tip)))))))"
```

This exact conclusion is an `all_distinct` fact for a tree of translated
function addresses.  It mentions none of `pxReadyTasksLists_'`,
`xDelayedTaskList1_'`, `xDelayedTaskList2_'`,
`xPendingReadyList_'`, or `xSuspendedTaskList_'`.  It therefore does not
directly establish object-interval separation for the eight physical list
roots, and it supplies no ready-array element interval lemma.

## Cross-parser type-universe diagnostic

The independent raw-list relation and the scheduler translation share the
same byte-heap carrier but not the generated C struct types.  The final,
checker-green heap-compatibility term prints:

```isabelle
"\<lambda>c. raw_xlist_rel (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
:: "Scheduler_V611_Parse.globals \<Rightarrow>
    List_V611_Raw_Skip_Translation.xLIST_C ptr \<Rightarrow>
    (List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr, 32 word) xlist_abs
      \<Rightarrow> bool"

"raw_xlist_rel"
:: "(32 word \<Rightarrow> 8 word) \<Rightarrow>
    List_V611_Raw_Skip_Translation.xLIST_C ptr \<Rightarrow>
    (List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr, 32 word) xlist_abs
      \<Rightarrow> bool"
```

The first term was accepted before the later item diagnostic failed.  In
particular, scheduler `hrs_mem` has the same effective
`32 word \<Rightarrow> 8 word` type required by `raw_xlist_rel`.

The direct root application was rejected with:

```text
Clash of types "Scheduler_V611_Parse.xLIST_C"
and "List_V611_Raw_Skip_Translation.xLIST_C"
```

The separately isolated abstract-node application was rejected with:

```text
Clash of types "List_V611_Raw_Skip_Translation.xLIST_ITEM_C"
and "Scheduler_V611_Parse.xLIST_ITEM_C"
```

The final green theory also prints the four distinct pointer types side by
side.  Consequently, the general raw-list theorem cannot be applied directly
to a scheduler root or scheduler item.  Reuse needs an explicit
translation-unit ABI/type bridge, or the list representation and theorem must
be reconstructed in the scheduler parser universe.  This diagnostic does not
choose or implement either route.

## Post-build disposition of the pre-build unresolved list

1. **Resolved:** the ready base is an array-of-four pointer and all four
   standalone addressed roots are `Scheduler_V611_Parse.xLIST_C ptr`; the
   locale context is printed above.
2. **Partly resolved:** the three field offsets and TCB size are exact above.
   Alignment remains unprobed.
3. **Resolved negatively:** the printed `all_distinct` fact is about function
   addresses and does not prove physical root separation.  Global-object and
   ready-array-element interval separation remain unresolved.
4. **Unresolved:** no guarded-TCB containment theorem or generic/event
   embedded-region disjointness theorem has been stated or proved.
5. **Unresolved:** the forward TCB-pointer-to-`unit ptr` owner coercion has
   not been frozen.

The source definition commands in the candidate list were also accepted, but
their large equations are not duplicated here; they remain in the hashed PIDE
stream.

## Build, cost, hashes, and forbidden scan

All calls used the project wrapper, one job, a 180-second external bound, and
`quick_and_dirty=false`.

| Run | Result | Seconds | Diagnostic / evidence | `stdout.log` SHA-256 |
|---|---:|---:|---|---|
| `20260731Tscheduler-p2-layout-first-01-direct-reuse-diagnostic` | 1 | 58.272 | exposed raw versus scheduler `globals_scheme` selection; scheduler selectors were then qualified | `8292D0EFC32142E2F90FAA09C641F181860A25442A326BFDBE42DCCFF109FDDE` |
| `20260731Tscheduler-p2-layout-first-02-qualified-state` | 1 | 59.979 | exact `xLIST_C` clash on direct scheduler-root reuse | `F2E7A358198F31F2D2915E19FEDE32C8FE7243BC70ABFA12AB6A8F23A38834B7` |
| `20260731Tscheduler-p2-layout-first-03-heap-item-diagnostic` | 1 | 59.457 | heap term passed; exact `xLIST_ITEM_C` clash followed | `20DBF2E48E82F7C4F0D1D63D13B03A00926AC136593B6B9408B0A31562A998B9` |
| `20260731Tscheduler-p2-layout-first-04-green` | 0 | 58.491 | final diagnostic leaf checker-green | `85255AB913C35001C358BED2F1F88DB7849B7C29D3FA1A090D3B55DA19E21249` |

The four bounded calls cost exactly 236.199 seconds in total: three retained
diagnostic red calls and one final green call.  The export then used
`isabelle export -n`, so it performed no build.

| Final artifact | SHA-256 |
|---|---|
| `Scheduler_P2_Generated_Layout_First.thy` | `604A4BCCE04F39AFC499A3F58BC9DD65F7E31A57CA8AB526467DB645FFA8F843` |
| `theories/ROOT` | `8D79643FEC0E4CE7EB95C0FB3CE53FCF674D45FC5E452B4E09939A943AC551AE` |
| `scripts/build-list-smoke.ps1` | `3EE0F0E5CC1E9D91113E0465EED551CE752AE4B9F4F5E1593B0F93F5173FD733` |
| final `status.txt` | `E022F1D429064BB06F787D5278660637A1B2A9CAFDA89781F6AA8FDB70AD40E1` |
| final `PIDE/messages` export | `1332C8677E07150F9FF461866AACF86FBA58C1BB63C38A175E7FD86BD662C553` |

A targeted case-insensitive scan of the new theory, `theories/ROOT`, and the
build wrapper for
`sorry|oops|axiomatization|oracle|admit|quick_and_dirty=true` returned no
matches (`rg` exit 1).  The final PIDE stream contains no `warning_message` or
`error_message` tag, and `isabelle build_log -H Error` is empty for the green
session.  No original formalisation was opened, and no mapping document or
`theories/scheduler_raw_list_relabel` file was modified.
