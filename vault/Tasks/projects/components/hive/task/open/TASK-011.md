# TASK-011: CocoTB SERV Core Testbench

> Migrated 2026-09-25 from `projects/components/hive/TASKS.md`
> as **TASK-011** (tooling TOOL-001), ID unchanged. Classified against the
> tree: hive has ZERO `.sv` files, zero tests, no SERV or VexRiscv source,
> and only `ch01_overview/` plus `ch02_blocks/00_overview.md` written -- so
> every item except TASK-000 is genuinely open, and each item's stated
> Related Files path does not exist yet.

**Status:** Planned
**Priority:** P1
**Effort:** 4 days
**Owner:** Unassigned

**Description:**
Create comprehensive CocoTB testbench for SERV wrapper testing.

**Acceptance Criteria:**
- [ ] Create ServWrapperTB class in bin/TBClasses/hive/
- [ ] Implement instruction memory loader
- [ ] Run basic RISC-V ISA tests (ADD, SUB, LOAD, STORE)
- [ ] Verify bit-serial execution timing
- [ ] Test CSR access
- [ ] Create test_serv_wrapper.py with >85% coverage

**Dependencies:**
- TASK-006 (SERV integration)

**Related Files:**
- `val/hive/test_serv_wrapper.py`
- `bin/TBClasses/hive/serv_wrapper_tb.py`

---
