# TASK-014: CocoTB System Integration Testbench

> Migrated 2026-09-25 from `projects/components/hive/TASKS.md`
> as **TASK-014** (tooling TOOL-001), ID unchanged. Classified against the
> tree: hive has ZERO `.sv` files, zero tests, no SERV or VexRiscv source,
> and only `ch01_overview/` plus `ch02_blocks/00_overview.md` written -- so
> every item except TASK-000 is genuinely open, and each item's stated
> Related Files path does not exist yet.

**Status:** Planned
**Priority:** P1
**Effort:** 1 week
**Owner:** Unassigned

**Description:**
Create end-to-end HIVE system testbench with VexRiscv supervising 16 SERV cores.

**Acceptance Criteria:**
- [ ] Create HiveSystemTB class
- [ ] Load boot ROM with VexRiscv supervisor code
- [ ] Load SERV programs (parallel tasks)
- [ ] Test VexRiscv → SERV task dispatch
- [ ] Verify shared memory access coordination
- [ ] Measure system throughput
- [ ] Create test_hive_system_integration.py

**Dependencies:**
- TASK-010 (HIVE top-level)
- TASK-011 (SERV testbench)
- TASK-012 (VexRiscv testbench)
- TASK-013 (Arbiter testbench)

**Related Files:**
- `val/hive/test_hive_system_integration.py`
- `bin/TBClasses/hive/hive_system_tb.py`

---
