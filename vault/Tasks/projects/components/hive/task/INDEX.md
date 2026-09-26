<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/hive — tasks

**Next ID: TASK-026** — never recycle a number, even when its item closed.

planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 25 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |

## Open

- **TASK-000** — reserved template; copy the file, do not file against it.
- **TASK-001** — Complete Specification Chapter 2 (SERV Core)
- **TASK-002** — Complete Specification Chapter 2 (VexRiscv Core)
- **TASK-003** — Complete Specification Chapter 3 (Memory Subsystem)
- **TASK-004** — Complete Specification Chapter 4 (Interconnect)
- **TASK-005** — Complete Specification Chapter 5 (System Integration)
- **TASK-006** — SERV Core Integration
- **TASK-007** — VexRiscv Core Integration
- **TASK-008** — Shared Memory Subsystem RTL
- **TASK-009** — AXI4-Lite Interconnect RTL
- **TASK-010** — HIVE Top-Level Integration
- **TASK-011** — CocoTB SERV Core Testbench
- **TASK-012** — CocoTB VexRiscv Core Testbench
- **TASK-013** — CocoTB Memory Arbiter Testbench
- **TASK-014** — CocoTB System Integration Testbench
- **TASK-015** — Software Toolchain Setup
- **TASK-016** — Wavedrom Timing Diagrams
- **TASK-017** — PlantUML FSM Diagrams
- **TASK-018** — Block Diagrams and Architecture Images
- **TASK-019** — Performance Monitoring
- **TASK-020** — Hardware Task Scheduler
- **TASK-021** — DMA Support
- **TASK-022** — Peripheral Integration
- **TASK-023** — Debugging Infrastructure
- **TASK-024** — Power Management

## Closed

- **TASK-025** — Initial Specification Structure (Complete - 2025-10-15)
