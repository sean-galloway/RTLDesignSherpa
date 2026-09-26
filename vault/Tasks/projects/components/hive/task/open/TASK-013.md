# TASK-013: CocoTB Memory Arbiter Testbench

> Migrated 2026-09-25 from `projects/components/hive/TASKS.md`
> as **TASK-013** (tooling TOOL-001), ID unchanged. Classified against the
> tree: hive has ZERO `.sv` files, zero tests, no SERV or VexRiscv source,
> and only `ch01_overview/` plus `ch02_blocks/00_overview.md` written -- so
> every item except TASK-000 is genuinely open, and each item's stated
> Related Files path does not exist yet.

**Status:** Planned
**Priority:** P1
**Effort:** 3 days
**Owner:** Unassigned

**Description:**
Create testbench for shared memory arbiter with multiple master stimuli.

**Acceptance Criteria:**
- [ ] Create MemoryArbiterTB class
- [ ] Implement 17 AXI master BFMs
- [ ] Test priority arbitration (VexRiscv > SERV)
- [ ] Test round-robin among SERV cores
- [ ] Measure arbitration latency and fairness
- [ ] Create test_hive_mem_arbiter.py

**Dependencies:**
- TASK-008 (Memory arbiter implementation)

**Related Files:**
- `val/hive/test_hive_mem_arbiter.py`
- `bin/TBClasses/hive/mem_arbiter_tb.py`

---
