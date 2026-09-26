<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/delta — tasks

**Next ID: TASK-017** — never recycle a number, even when its item closed.

planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 14 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 3 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |

## Open

- **TASK-000** — reserved template; copy the file, do not file against it.
- **TASK-003** — Router RTL Implementation
- **TASK-004** — Network Interface RTL Implementation
- **TASK-005** — Mesh Topology RTL Implementation
- **TASK-006** — CocoTB Router Testbench
- **TASK-007** — CocoTB Mesh Integration Testbench
- **TASK-008** — Wavedrom Timing Diagrams
- **TASK-009** — PlantUML FSM Diagrams
- **TASK-010** — Block Diagrams and Architecture Images
- **TASK-011** — Performance Monitoring Integration
- **TASK-012** — Adaptive Routing Support
- **TASK-013** — Quality-of-Service (QoS)
- **TASK-014** — Larger Mesh Topologies
- **TASK-015** — Fault Tolerance

## Closed

- **TASK-001** — Complete Specification Chapter 4 (Routing Algorithm)
- **TASK-002** — Complete Specification Chapter 5 (Flow Control)
- **TASK-016** — Initial Specification Structure (Complete - 2025-10-15)
