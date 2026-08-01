# Toolchain lock

## Discovered local toolchain

- Isabelle: `Isabelle2025-2`
- Isabelle home: `C:\Isabelle2025-2\Isabelle2025-2`
- AFP checkout: `C:\afp25\afp-2026-07-21`
- AutoCorres2 session: `AutoCorres2_Main`
- AutoCorres2 source: AFP entry under `thys\AutoCorres2`
- ML runtime: Poly/ML 5.9.2, confirmed on the
  `polyml-5.9.2_x86_64_32-windows` session-store platform by the final list
  smoke database
- shell: Isabelle-bundled Cygwin bash
- required build option: `quick_and_dirty=false`

The AFP short path is load-bearing on Windows: the C parser's generated lexer
paths can exceed the platform path limit when AFP is nested deeply.

No Isabelle build may be unbounded.  Only one live build owned by this project
is allowed.  Stable checker-green rungs are promoted to parent sessions; the
active theory remains in a small child session.

The Windows launcher recomputes `ISABELLE_HOME_USER` from its settings; merely
exporting that variable before `bin/isabelle` does not relocate the session
database. Current bounded runs therefore use the default
`C:\Users\Chengsong\.isabelle\Isabelle2025-2` store and are serialized across
all project workers. A future private store must set an audited `USER_HOME`
before launcher startup and rebuild its dependencies; existing runs must not
be described as private-home runs.
