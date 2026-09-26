# TASK-009: AXI4-Lite Interconnect RTL

> Migrated 2026-09-25 from `projects/components/hive/TASKS.md`
> as **TASK-009** (tooling TOOL-001), ID unchanged. Classified against the
> tree: hive has ZERO `.sv` files, zero tests, no SERV or VexRiscv source,
> and only `ch01_overview/` plus `ch02_blocks/00_overview.md` written -- so
> every item except TASK-000 is genuinely open, and each item's stated
> Related Files path does not exist yet.

**Status:** Planned
**Priority:** P0
**Effort:** 3 days
**Owner:** Unassigned

**Description:**
Implement AXI4-Lite crossbar connecting VexRiscv, SERV cores, and peripherals.

**Acceptance Criteria:**
- [ ] Implement hive_interconnect.sv (AXI4-Lite crossbar)
- [ ] Add address decoder for peripheral routing
- [ ] Implement multi-master arbitration
- [ ] Support 1 VexRiscv + 16 SERV masters
- [ ] Support 4+ slave devices (SRAM, ROM, UART, GPIO)
- [ ] Verify interconnect with CocoTB

**Dependencies:**
- TASK-004 (Interconnect spec)

**Related Files:**
- `rtl/hive/hive_interconnect.sv`

---
