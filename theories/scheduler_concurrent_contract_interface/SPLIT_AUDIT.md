# Concurrent contract staircase split audit

This is a static, mechanical audit of the session split. No Isabelle build,
proof search, or generated-source execution was run while producing it.

## Source reconstruction

- Pre-split source SHA-256:
  `95AF5E8A884BF3C36A21FEA1DE42813B56AD1D24F95AD084FE0AF97B0B985F5B`
- Reconstruction: concatenate the six split theory bodies in dependency order,
  restore the original `Scheduler_Concurrent_Contract_Interface` header and
  imports, append the original final `end`, encode as UTF-8 with LF and one
  trailing newline.
- Reconstructed SHA-256:
  `95AF5E8A884BF3C36A21FEA1DE42813B56AD1D24F95AD084FE0AF97B0B985F5B`
- Original/reconstructed line count: 1075.
- Result: exact byte identity under the source's original LF encoding.

## Declaration ledger

The ordered ledger is [SPLIT_DECLARATION_LEDGER.tsv](SPLIT_DECLARATION_LEDGER.tsv).

- Total declarations: 82.
- Missing declarations: 0.
- Extra declarations: 0.
- Order mismatches: 0.
- Duplicate base names: 0.
- Semantic `kind<TAB>name` ledger SHA-256:
  `B643ABCE87BEEB46CCF9DB04B3E9ADD7CDD876E00B1E2C66A99BCCA036E572AC`
- Ledger file SHA-256:
  `30B4E1B25AC7B519AB6D44B0EDFCA320DB4D1EFFB6C39DEAF380F1F3BFEA1919`

| Layer | Declarations |
|---|---:|
| state | 23 |
| environment step | 17 |
| environment closure | 8 |
| program step | 9 |
| interleaving | 5 |
| cutpoint | 20 |

## Session ledger

There are seven sessions in seven distinct directories. Every session declares
`quick_and_dirty = false`, `parallel_proofs = 0`, and `timeout = 120`.
The last session retains the original
`EAL6_FreeRTOS_V611_Scheduler_Concurrent_Contract_Interface` name and the
original theory name is a thin compatibility facade.

| File | SHA-256 |
|---|---|
| `state/Scheduler_Concurrent_State.thy` | `87A1B3526D2BA0B9D0B4AC1B65626F5D5938DF76E1CF24CC5ADE0B5E834DCC9F` |
| `environment_step/Scheduler_Concurrent_Environment_Step.thy` | `3A3780779395E7229B971694A2F844B1A5F70EA9460C7A06C206D24DEEBACA3D` |
| `environment_closure/Scheduler_Concurrent_Environment_Closure.thy` | `C7DD7D5E524C1FD67ABE6A046F86F8A66E225AB2F88B0EF89A0EB1FF89464B6A` |
| `program_step/Scheduler_Concurrent_Program_Step.thy` | `B72C5CC59E9906B592DE1E03770A03E6195792ABE5BCD2D6A86F3F61D93F2CA7` |
| `interleaving/Scheduler_Concurrent_Interleaving.thy` | `FB85D673065DDF97DCDF55654C39E5A9331437BEEFE24695298818FBB25A20E4` |
| `cutpoint/Scheduler_Concurrent_Cutpoint.thy` | `AD2B217EB59326541DA124A13A5A43BE4BC0AAC8F2D44CA21347619B1DA65463` |
| `Scheduler_Concurrent_Contract_Interface.thy` | `43FA4813D1614F87D7C0DD39B021274C844A401E11BA6D8C3D94418664CFFB62` |
| `ROOT` | `1187BC62EBFEE17DCD7597929183C02BD0C1D354BC15437D8419581D6646DBDB` |

Static scans found no `sorry`, `oops`, `axiomatization`, `oracle`,
`admit`, or reserved local fact named `open`. Dynamic checker status remains
intentionally unclaimed until the sessions are built.

