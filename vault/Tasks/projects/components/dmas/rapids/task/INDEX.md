<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/dmas/rapids — tasks

**Next ID: TASK-007** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 5 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |

## Open

- **TASK-000** — reserved template; copy the file, do not file against it.
- **TASK-003** — scrub the tests for completeness (rapids)

## Closed

- **TASK-002** — RAPIDS-beats has NO contracts workbook at all
- **TASK-001** — adopt the shared instrumentation pair (axi4_intf_master_observer + dma_slave_monitors)
- **TASK-004** — Register-map hygiene enforced in RAPIDS DV
- **TASK-005** — one RTL harness -- move the host path down so verify-sim can reach it
- **TASK-006** — re-measure the beat-count knee on rapids (July data is stale)
