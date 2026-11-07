<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/fpga-systems/NexysA7/misc-ip/cdc_counter_display — tasks

**Next ID: TASK-006** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 4 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-002** — sim carries a value through every CDC mode (today only mode 0; modes 1-4 are board-proven only)
- **TASK-003** — measured comparison of the five modes: area, latency, throughput
- **TASK-004** — single-bit `cdc_synchronizer` demonstration (decide first whether it teaches anything new)
- **TASK-005** — metastability injector so RTL sim shows mode 0 failing

## Active

(none)

## Deferred

(none)

## Closed

- **TASK-001** — CDC demo build plan delivered as one top with five runtime CDC modes; board-validated 2026-09-08 (migrated from docs/CDC_DEMO_TODO.md 2026-11-07)
