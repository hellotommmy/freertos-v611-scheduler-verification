# Toolchain lock

## Discovered local toolchain

- Isabelle: `Isabelle2025-2`
- Isabelle home: `C:\Isabelle2025-2\Isabelle2025-2`
- AFP checkout: `C:\afp25\afp-2026-07-21`
- audited upstream AutoCorres2 source: the AFP entry under
  `thys\AutoCorres2`, left unmodified;
- project-local patched sessions: `AutoCorres2_P2_Layout` and
  `AutoCorres2_P2_Layout_Main`, staged under
  `build\autocorres2-p2-layout` by
  `scripts\prepare-patched-autocorres2.ps1`;
- ML runtime: Poly/ML 5.9.2, confirmed on the
  `polyml-5.9.2_x86_64_32-windows` session-store platform by the final list
  smoke database
- shell: Isabelle-bundled Cygwin bash
- required build option: `quick_and_dirty=false`

## Addressed-global patch lock

The project does not modify the installed AFP checkout.  The preparation
script first verifies the upstream `c-parser\calculate_state.ML`, copies the
AutoCorres2 entry into the ignored project build tree, and applies the audited
patch there.  The patch adds the string option
`c_parser_addressed_global_definitions`, checks that a nonempty supplied map
exactly covers the addressed-data globals found by CParser, rejects malformed,
duplicate, out-of-range, missing, or extra entries, and emits pointer
definitions for the configured addresses.  Without a supplied map, the
ordinary upstream unconstrained-constant route remains available in the
separately named local sessions.

Current SHA-256 lock values, recomputed from the files on disk, are:

| Object | SHA-256 |
|---|---|
| upstream `c-parser/calculate_state.ML` | `EA51ECAA01947E53AD38A684B0E97ED360339363A75C6AE16DCFBA7713562898` |
| `patches/autocorres2-addressed-global-definitions.patch` | `44160F97B133D0A66E515E505636D641907DC14811D43DA071EA15C706C8E604` |
| staged patched `c-parser/calculate_state.ML` | `FD244D8228E79EC3626A5CE312446CE49DF550970B758B68D3BBE953CAC8CFA9` |
| frozen `frozen_p2_layout.elf` | `DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A` |
| `layout_ledger.json` | `CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02` |
| generated `P2_Root_Address_Config.ML` | `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712` |

The generated configuration exactly maps these six C bases:
`pxReadyTasksLists`, `xDelayedTaskList1`, `xDelayedTaskList2`,
`xPendingReadyList`, `xSuspendedTaskList`, and
`xTasksWaitingTermination`.  The 80-byte ready-array base contributes four
20-byte list regions; the other five bases contribute one each.  Thus the
six mapped bases derive nine static `xLIST` regions.  Eight are the P2
relation roots; the ninth is the termination-wait list used for exact CParser
coverage but not by the P2 relation.

This is a local, reviewable adaptation of the translation tool, not a proof
of the toolchain.  The fixed-address ELF is never executed.  GCC, assembler,
linker, `readelf`, `nm`, CParser, AutoCorres2, Isabelle, and Poly/ML remain in
the trusted computation base appropriate to their recorded evidence.  The
two P2 task control blocks are logical runtime witnesses, not fixed-address
ELF symbols.

## Portable seal replay

Every final run status records the same ELF/ledger/configuration hashes above,
`quick_and_dirty=false`, `timed_out=false`, and exit code 0:

| Session gate | Run | Seconds |
|---|---|---:|
| addressed-global scheduler parse | `20260801Tseal-scheduler-parse-01-portable` | 23.566 |
| ordinary CParser layout no-go | `20260801Tseal-p2-layout-no-go-01-portable` | 33.162 |
| frozen nine-region static geometry | `20260801Tseal-p2-static-nine-01-portable` | 27.701 |
| fresh-TCB dynamic geometry against all nine | `20260801Tseal-p2-dynamic-all-nine-01-portable` | 27.467 |
| artifact-bound P2 preimage/refinement seal | `20260801Tseal-p2-preimage-06-parenthesised-seal` | 120.854 |
| literal four-call list chain | `20260801Tseal-list-four-call-01-portable` | 32.338 |
| stock list translation smoke | `20260801Tseal-list-smoke-01-portable` | 67.973 |
| raw `skip_heap_abs` list translation | `20260801Tseal-list-raw-skip-01-portable` | 22.551 |

The theorem inventory sealed by these and the earlier checked dependency
sessions totals 13 source-to-abstract refinements, 8 distinct operations, and
2 sequential compositions.  The four-call theorem contains exactly three
`runs_to_bind` proof steps and has no assumptions; its interface makes no
`tail8` claim.  The artifact-bound real `vTaskDelay' 2` theorem ends at
`YieldPending`.

The AFP short path is load-bearing on Windows: the C parser's generated lexer
paths can exceed the platform path limit when AFP is nested deeply.

No Isabelle build may be unbounded.  Only one live build owned by this project
is allowed.  Stable checker-green rungs are promoted to parent sessions; the
active theory remains in a small child session.

The Windows launcher recomputes `ISABELLE_HOME_USER` from its settings; merely
exporting that variable before `bin/isabelle` does not relocate the session
database. Current bounded runs therefore use the default
`%USERPROFILE%\.isabelle\Isabelle2025-2` store and are serialized across
all project workers. A future private store must set an audited `USER_HOME`
before launcher startup and rebuild its dependencies; existing runs must not
be described as private-home runs.

The lock deliberately makes no claim about allocator behaviour, task-object
construction, boot or scheduler-start reachability, compiler correctness,
execution of the pending context switch, machine-code correctness,
binary-to-source equivalence, a deployed port, or whole-scheduler refinement.
Those subjects remain outside the frozen artifact and proof scope.
