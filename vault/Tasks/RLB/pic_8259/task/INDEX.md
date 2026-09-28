<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# RLB/pic_8259 — tasks

**Next ID: TASK-002** — never recycle a number, even when its item closed.

planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-000** — reserved template; copy the file, do not file against it.

## Closed

- **TASK-001** — 8259 cascade complete: a two-PIC PC/AT DV wrapper with six tests, the slave PIC on rlb_top window 9 (xbar NOT regenerated), IRQ8-15 now exist. 3 suites green, closed 2026-09-28.
