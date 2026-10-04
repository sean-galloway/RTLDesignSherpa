<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# andesite-ddr4-lpddr4 — tasks

**Next ID: TASK-006** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 5 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-001** — advanced scheduling / refresh modes survey.
- **TASK-002** — author the andesite HAS v0.1 and the family docs seed
  (`mem-ctrl-ip/docs/`); closes when the HAS is owner-reviewed complete at
  v0.1 and the seed is committed.
- **TASK-003** — author the andesite MAS v0.1 (changed/new blocks in depth;
  inherited blocks referenced to scoria's books); closes when owner-reviewed
  complete.
- **TASK-004** — author the andesite kmap book (command truth tables, decode
  maps, MR0-6 programming maps; generator-gated, cited from MAS/HAS); closes
  when the tables land and the citation gate is green.
- **TASK-005** — DFI 4.0 spec acquisition + BFM study; the spec is not on
  disk, so every DFI 4.0 claim in the books carries `§TBC(TASK-005)` until
  this confirms clause numbers and a BFM exists.
