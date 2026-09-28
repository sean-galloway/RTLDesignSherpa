<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# amba/monitor-lite — tasks

**Next ID: TASK-004** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 2 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-000** — reserved template; copy the file, do not file against it.
- **TASK-002** — run the inherited monitor suites against the lite with per-class skips

## Active

- **TASK-003** — axis_monitor_lite: a stream monitor core in the lite discipline (there has never been an AXIS monitor), plus the axis4/axis5 master/slave monlite wrappers -- core DONE 2026-09-27 (12/12 FULL, mutation-checked); wrappers next
- **TASK-001** — monitor-lite -- three quarters of the AXI monitor for a fifth of the gates (built and measured 2026-09-25: 677 vs 3,249 LUTs)
