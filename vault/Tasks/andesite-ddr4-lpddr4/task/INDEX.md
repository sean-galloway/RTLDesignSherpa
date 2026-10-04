<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# andesite-ddr4-lpddr4 — tasks

**Next ID: TASK-006** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 3 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 2 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-001** — advanced scheduling / refresh modes survey.
- **TASK-004** — author the andesite kmap book (command truth tables, decode
  maps, MR0-6 programming maps; generator-gated, cited from MAS/HAS); closes
  when the tables land and the citation gate is green.
- **TASK-005** — DFI 4.0 spec acquisition + BFM study; the spec is not on
  disk, so every DFI 4.0 claim in the books carries `§TBC(TASK-005)` until
  this confirms clause numbers and a BFM exists.

## Closed

- **TASK-003** — author the andesite MAS v0.1: closed 2026-10-04; the
  `andesite_mas/` book is complete at v0.1 and owner-reviewed, with the DFI
  4.0 pin table and the contract anchors the kmap book cites.
- **TASK-002** — author the andesite HAS v0.1 and the family docs seed:
  closed 2026-10-04; the `andesite_has/` book is complete at v0.1 and
  owner-reviewed, and the `mem-ctrl-ip/docs/` family seed is committed.
