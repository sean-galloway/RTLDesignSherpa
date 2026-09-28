<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/dmas/rapids — tasks

**Next ID: TASK-018** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 16 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-000** — reserved template; copy the file, do not file against it.
- **TASK-017** — rapids placement pass: 6 loose filelists (dv/tb + Genesys2 flists/) and 13 loose markdown files

## Active

## Closed

- **TASK-001** — adopt the shared instrumentation pair (axi4_intf_master_observer + axis4_intf_observer); measured through them 2026-09-27
- **TASK-002** — RAPIDS-beats has NO contracts workbook at all
- **TASK-004** — Register-map hygiene enforced in RAPIDS DV
- **TASK-005** — one RTL harness -- move the host path down so verify-sim can reach it
- **TASK-006** — re-measure the beat-count knee on rapids (July data is stale)
- **TASK-007** — MAS/HAS trees and index table redrawn to the STREAM-wrapper hierarchy (closed 2026-09-27)
- **TASK-008** — ch01_overview/02_port_list.md regenerated from the RTL: 300/300 ports, per half (closed 2026-09-27)
- **TASK-009** — 07_beats_latency_bridge.md re-authored against latency_bridge_beats.sv (closed 2026-09-27)
- **TASK-011** — 15 `// Module:` headers now match their filenames (closed 2026-09-27)
- **TASK-012** — harness AXI observer timestamp FIFO 8 -> 32; latency sweep re-measured with no sample loss (closed 2026-09-27)
- **TASK-003** — scrub the tests for completeness (rapids) (closed 2026-09-27; residue is TASK-013)
- **TASK-013** — replace the hand-rolled protocol responders in the rapids TBs with framework BFMs (closed 2026-09-27)
- **TASK-010** — 26 ASCII placeholder figures name dead signals; 2 figures have no test to capture from (closed 2026-09-27)
- **TASK-014** — control engines drain on channel reset instead of abandoning the AXI transaction (closed 2026-09-27)
- **TASK-015** — AXIS monitor-lite in each half (Option B), one arbiter entry per half (closed 2026-09-27)
- **TASK-016** — re-prove the rapids and stream formal suites after the engine fixes; prove the control engines (closed 2026-09-28)
