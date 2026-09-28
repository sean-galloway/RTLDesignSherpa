<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# common — tasks

**Next ID: TASK-016** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 12 | done (kept for history) |
| [dropped/](dropped/) | 2 | ended without completing |
| [deferred/](deferred/) | 1 | parked pending a named condition |

## Open


## Closed

- **TASK-011** — scrub the tests for completeness (common)
- **TASK-001** — Improve test coverage to 95%
- **TASK-002** — Waveform save files for all modules
- **TASK-003** — Integration examples (became the technique index)
- **TASK-004** — Documentation consistency review
- **TASK-005** — Parameterization audit
- **TASK-006** — Multi-byte CRC support
- **TASK-007** — Every module MUST have a filelist and a registry entry
- **TASK-008** — Update formal for common: staleness audit + re-prove + cover closure
- **TASK-009** — Signal-prefix sweep: make r_/w_ truthful across the library
- **TASK-010** — close the measured line-coverage gaps
- **TASK-014** — COMMON-ORPHANS — two harnesses for RTL deleted a month earlier

## Dropped

- **TASK-012** — Configurable-width adders/multipliers
- **TASK-013** — BCH and Reed-Solomon ECC

## Deferred

- **TASK-015** — Additional arbiter types
