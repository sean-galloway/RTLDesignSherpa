# TASK-023: STREAM v1.0 -- APB configuration, top-level wrapper, integration tests

> Migrated 2026-11-07 from `projects/components/dma-ip/stream/TASKS.md`, which recorded these as **TASK-001 / TASK-002 / TASK-003** in its milestone list. Those numbers collide with this lane's own TASK-001..003 (different work), so the v1.0 ledger is kept as one closed item here.

**Priority:** P1 (v1.0 critical path)
**Status:** CLOSED 2025-11-30 -- STREAM v1.0 complete.
**Owner:** sean galloway

## Milestones, as the old file recorded them

- 2025-10-19 initial RTL structure
- 2025-10-28 AXI engine V2 design
- 2025-11-09 APB configuration interface (PeakRDL `stream_regs`) -- old TASK-001
- 2025-11-10 parameter unification
- 2025-11-11 write-engine bubble-free pipeline; AXI completion tracking; datapath and core tests passing
- 2025-11-24 top-level wrapper `stream_top_ch8.sv` -- old TASK-002 (fcfac0be0)
- 2025-11-30 final integration tests (`test_stream_top*`) -- old TASK-003

## The old file's "enhancement ideas", disposed

| Idea | Disposition |
|---|---|
| Circular buffer support; 2D / strided / scatter addressing | Delivered by [TASK-022](TASK-022.md) (was TASK-101) |
| Interrupt generation | Exists: a descriptor with `gen_irq` emits a MonBus `STREAM_EVENT_IRQ` completion packet (`rtl/fub/scheduler_core.sv`), and `stream_irq` pulses per error record (`monbus_axil4_group_1wr`) |
| Alignment fixup ("STREAM Extended") | Not filed: excluded by STREAM's tutorial rule (stream CLAUDE.md Rule #0.1, aligned addresses only; RAPIDS has fixup) |
| "Performance optimization for specific use cases", "additional MonBus event types" | Not filed: no scope, no consumer. File a task when one exists |
