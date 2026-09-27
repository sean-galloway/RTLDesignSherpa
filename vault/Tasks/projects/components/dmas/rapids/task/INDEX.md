<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/dmas/rapids — tasks

**Next ID: TASK-012** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 7 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 5 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |

## Open

- **TASK-000** — reserved template; copy the file, do not file against it.
- **TASK-003** — scrub the tests for completeness (rapids)
- **TASK-007** — the MAS/HAS trees and index table describe the pre-wrapper SRAM architecture
- **TASK-008** — ch01_overview/02_port_list.md documents 86 of 300 ports, mis-structured
- **TASK-009** — 07_beats_latency_bridge.md documents the wrong CONCEPT
- **TASK-010** — 26 ASCII placeholder figures name dead signals; 2 figures have no test to capture from
- **TASK-011** — 15 rapids .sv files carry a `// Module:` header that contradicts their own filename

## Active

## Closed

- **TASK-001** — adopt the shared instrumentation pair (axi4_intf_master_observer + axis4_intf_observer); measured through them 2026-09-27
- **TASK-002** — RAPIDS-beats has NO contracts workbook at all
- **TASK-004** — Register-map hygiene enforced in RAPIDS DV
- **TASK-005** — one RTL harness -- move the host path down so verify-sim can reach it
- **TASK-006** — re-measure the beat-count knee on rapids (July data is stale)
