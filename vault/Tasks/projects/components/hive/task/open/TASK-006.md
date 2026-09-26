# TASK-006: SERV Core Integration

> Migrated 2026-09-25 from `projects/components/hive/TASKS.md`
> as **TASK-006** (tooling TOOL-001), ID unchanged. Classified against the
> tree: hive has ZERO `.sv` files, zero tests, no SERV or VexRiscv source,
> and only `ch01_overview/` plus `ch02_blocks/00_overview.md` written -- so
> every item except TASK-000 is genuinely open, and each item's stated
> Related Files path does not exist yet.

**Status:** Planned
**Priority:** P0
**Effort:** 1 week
**Owner:** Unassigned

**Description:**
Integrate SERV bit-serial RISC-V core as submodule and create wrapper with AXI4-Lite interface.

**Acceptance Criteria:**
- [ ] Add SERV repository as git submodule
- [ ] Create serv_wrapper.sv with AXI4-Lite conversion
- [ ] Implement instruction memory interface
- [ ] Implement data memory interface
- [ ] Add configuration registers for SERV control
- [ ] Verify synthesizability with Verilator
- [ ] Document SERV integration in CLAUDE.md

**Dependencies:**
- TASK-001 (SERV spec)

**Related Files:**
- `rtl/hive/serv_wrapper.sv`
- `rtl/hive/serv/` (submodule)

---
