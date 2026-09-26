# TASK-008: Shared Memory Subsystem RTL

> Migrated 2026-09-25 from `projects/components/hive/TASKS.md`
> as **TASK-008** (tooling TOOL-001), ID unchanged. Classified against the
> tree: hive has ZERO `.sv` files, zero tests, no SERV or VexRiscv source,
> and only `ch01_overview/` plus `ch02_blocks/00_overview.md` written -- so
> every item except TASK-000 is genuinely open, and each item's stated
> Related Files path does not exist yet.

**Status:** Planned
**Priority:** P0
**Effort:** 4 days
**Owner:** Unassigned

**Description:**
Implement shared SRAM with multi-port arbiter for 1 VexRiscv + 16 SERV cores.

**Acceptance Criteria:**
- [ ] Implement hive_sram.sv (dual-port or banked SRAM)
- [ ] Implement hive_mem_arbiter.sv (17-to-1 arbiter)
- [ ] Add priority arbitration (VexRiscv > SERV)
- [ ] Implement round-robin among SERV cores
- [ ] Verify memory arbitration correctness
- [ ] Measure arbitration latency

**Dependencies:**
- TASK-003 (Memory subsystem spec)
- TASK-006 (SERV integration)
- TASK-007 (VexRiscv integration)

**Related Files:**
- `rtl/hive/hive_sram.sv`
- `rtl/hive/hive_mem_arbiter.sv`

---
