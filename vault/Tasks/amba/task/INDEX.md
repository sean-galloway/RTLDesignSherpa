<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# amba — tasks

**Next ID: TASK-041** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 6 | accepted, not started |
| [active/](active/) | 1 | in progress right now |
| [closed/](closed/) | 33 | done (kept for history) |
| [dropped/](dropped/) | 1 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-034** — Performance Characterization
- **TASK-035** — Make APB Crossbar Variants Functional
- **TASK-036** — Write Monitor System Whitepaper
- **TASK-037** — Lighten the gate-heavy monitor modules
- **TASK-038** — scrub the tests for completeness (amba)
- **TASK-000** — reserved template; copy the file, do not file against it.

## Active

- **TASK-039** — Update formal proofs for the monitor logic

## Closed

- **TASK-001** — Validate axi_monitor Base Functionality
- **TASK-002** — Integrate axi_monitor in AXI4 Master Read
- **TASK-003** — Integrate axi_monitor in AXI4 Master Write
- **TASK-004** — Integrate axi_monitor in AXI4 Slave Read
- **TASK-005** — Integrate axi_monitor in AXI4 Slave Write
- **TASK-006** — Validate All AXI4 Monitors (Without Clock Gating)
- **TASK-007** — Validate All AXI4 Monitors with Clock Gating
- **TASK-008** — Create AXIL Monitor (Adapt from AXI4)
- **TASK-009** — Integrate AXIL Monitor in All AXIL Modules
- **TASK-010** — Validate All AXIL Monitors (Without Clock Gating)
- **TASK-011** — Validate All AXIL Monitors with Clock Gating
- **TASK-012** — Fix Error Response and Orphan Detection Tests
- **TASK-013** — Create Integration Examples
- **TASK-014** — Add Address Range and ID Filtering
- **TASK-015** — AXI Monitor Test Validation and Refinement
- **TASK-016** — Add WaveDrom Support to APB Monitor Tests
- **TASK-017** — Add WaveDrom Support to AXI4 Monitor Tests
- **TASK-018** — Create GAXI Integration Tutorial Documentation
- **TASK-019** — Identify Tests That Would Benefit from WaveDrom
- **TASK-020** — Fix APB Monitor Core Functionality
- **TASK-021** — Complete rtl-amba Documentation and Waveform Integration
- **TASK-022** — Every module MUST have a filelist and a registry entry
- **TASK-023** — Split the address-range checker into independent DEBUG and ERROR range sets
- **TASK-024** — SPLIT axi4_intf_observer into master + slave versions; retire the original and dma_slave_monitors
- **TASK-025** — one module has no test coverage (was seven -- five of those claims were wrong)
- **TASK-026** — Wishbone B4 CTI/BTE burst hints on wb4_master / wb4_slave
- **TASK-027** — the four axi4 *_mon_cg formal proofs
- **TASK-028** — monitor-lite -- three quarters of the AXI monitor for a fifth of the gates
- **TASK-029** — move the last misplaced docs out of rtl/amba
- **TASK-030** — EXAMPLES — CLOSED 2026-08-27: resolved by deletion, plus the residue it left
- **TASK-031** — REORG — pull CDC out of amba into a top-level rtl/cdc area
- **TASK-032** — CONSISTENCY — normalize where .f lists live
- **TASK-033** — monitor side done (measured 2026-08-30); board-code residue noted

## Dropped

- **TASK-040** — TASKS — 4 open items removed from rtl/amba/PRD/ (2026-07-24)
