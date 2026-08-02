# Frozen P2 scheduler layout artifact

This directory builds the exact proof-port scheduler translation unit as a
fixed-address, freestanding ELF32/i386 artifact.  It does not modify either
FreeRTOS source body.  The artifact exists to extract and independently check
the six addressed scheduler-list base symbols used by the CParser model.  The
80-byte ready-array base expands to four 20-byte list regions and the other
five bases each contribute one region, giving nine static `xLIST` regions in
all.  Eight belong to the P2 relation; the ninth is the termination-wait list
that CParser also classifies as addressed data for exact-map coverage.

Run from PowerShell:

```powershell
./artifacts/frozen_p2_layout/build_and_check.ps1 -TimeoutSeconds 120
```

The bounded runner writes `output/frozen_p2_layout.elf`, a GNU ld map, DWARF
and symbol-table dumps, `layout_ledger.json`, `layout_report.txt`, complete
commands/tool versions, and `hashes.sha256`.  It rejects anything other than
ELF32 little-endian i386 `ET_EXEC`, rejects PIE/interpreter/dynamic sections,
and compares every base symbol's address and size through both `readelf` and
`nm`.  The four ready roots are derived twice from the independently extracted
80-byte array base using the checked 20-byte element stride.

The portable seal identity is:

| Object | SHA-256 |
|---|---|
| `output/frozen_p2_layout.elf` | `DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A` |
| `output/layout_ledger.json` | `CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02` |
| generated `P2_Root_Address_Config.ML` | `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712` |

The artifact is consumed through the audited exact-map CParser configuration.
Final portable runs check the specialized parse (23.566 s), nine-region
static geometry (27.701 s), dynamic TCB separation from all nine regions
(27.467 s), and the concrete P2 preimage/refinement seal (120.854 s).  Their
run IDs are respectively `20260801Tseal-scheduler-parse-01-portable`,
`20260801Tseal-p2-static-nine-01-portable`,
`20260801Tseal-p2-dynamic-all-nine-01-portable`, and
`20260801Tseal-p2-preimage-06-parenthesised-seal`; all record exit 0, no
timeout, and `quick_and_dirty=false`.  The ordinary unconstrained CParser
route remains separately checked as a no-go in
`20260801Tseal-p2-layout-no-go-01-portable` (33.162 s).

The link stubs close unreachable allocator, port-start, and C-library symbols;
they are not operational specifications and the ELF is never executed.  The
P2_IDLE and P2_RUN TCBs are fresh runtime logical witness objects, not ELF data
symbols.  The artifact alone supplies static scheduler-root layout evidence;
the external builder/generator validates it against the ledger and generated
configuration.  CParser then definitionally fixes those addresses, after which
Isabelle checks the source-semantic geometry and preimage obligations.  The
ELF-to-configuration correspondence is not an Isabelle theorem.  Neither the
artifact nor the final seal proves allocator or
task construction, boot or scheduler-start reachability, context-switch
execution, compiler or machine-code correctness, binary/source equivalence,
or full-scheduler correctness.
