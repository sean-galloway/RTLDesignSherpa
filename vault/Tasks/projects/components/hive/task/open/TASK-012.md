# TASK-012: CocoTB VexRiscv Core Testbench

> Migrated 2026-09-25 from `projects/components/hive/TASKS.md`
> as **TASK-012** (tooling TOOL-001), ID unchanged. Classified against the
> tree: hive has ZERO `.sv` files, zero tests, no SERV or VexRiscv source,
> and only `ch01_overview/` plus `ch02_blocks/00_overview.md` written -- so
> every item except TASK-000 is genuinely open, and each item's stated
> Related Files path does not exist yet.

**Status:** Planned
**Priority:** P1
**Effort:** 4 days
**Owner:** Unassigned

**Description:**
Create comprehensive CocoTB testbench for VexRiscv wrapper testing.

**Acceptance Criteria:**
- [ ] Create VexRiscvWrapperTB class
- [ ] Implement instruction/data cache BFMs
- [ ] Run RISC-V compliance tests
- [ ] Test interrupt handling
- [ ] Verify supervisor mode operations
- [ ] Create test_vexriscv_wrapper.py with >85% coverage

**Dependencies:**
- TASK-007 (VexRiscv integration)

**Related Files:**
- `val/hive/test_vexriscv_wrapper.py`
- `bin/TBClasses/hive/vexriscv_wrapper_tb.py`

---
