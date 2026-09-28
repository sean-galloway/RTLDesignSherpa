<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# amba/monitor-lite — tasks

**Next ID: TASK-005** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 3 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-000** — reserved template; copy the file, do not file against it.
- **TASK-004** — timeout and latency events lose the one-per-cycle pick to a sustained error stream; hold the payload until queued


## Active


## Closed

- **TASK-002** — run the inherited monitor suites against the lite with per-class skips -- CLOSED 2026-09-28: lite cells in all six inherited suites (28 cells + 108 area tests green from clean); two lite RTL defects fixed (same-cycle AW+W, early-beat count); timeout loss under an error flood measured and filed as TASK-004
- **TASK-001** — monitor-lite: three quarters of the AXI monitor for a fifth of the gates -- CLOSED 2026-09-28: everything landed by 2026-09-27; only the state was stale
- **TASK-003** — axis_monitor_lite core + the eight axis4/axis5 monlite wrappers -- CLOSED 2026-09-27
