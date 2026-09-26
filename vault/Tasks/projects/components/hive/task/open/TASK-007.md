# TASK-007: VexRiscv Core Integration

> Migrated 2026-09-25 from `projects/components/hive/TASKS.md`
> as **TASK-007** (tooling TOOL-001), ID unchanged. Classified against the
> tree: hive has ZERO `.sv` files, zero tests, no SERV or VexRiscv source,
> and only `ch01_overview/` plus `ch02_blocks/00_overview.md` written -- so
> every item except TASK-000 is genuinely open, and each item's stated
> Related Files path does not exist yet.

**Status:** Planned
**Priority:** P0
**Effort:** 1 week
**Owner:** Unassigned

**Description:**
Integrate VexRiscv supervisor core and configure for HIVE system requirements.

**Acceptance Criteria:**
- [ ] Add VexRiscv repository as git submodule
- [ ] Create vexriscv_wrapper.sv with AXI4 interface
- [ ] Configure VexRiscv with appropriate plugins (interrupts, caches)
- [ ] Implement supervisor mode features
- [ ] Add SERV coordination logic
- [ ] Verify synthesizability
- [ ] Document VexRiscv configuration

**Dependencies:**
- TASK-002 (VexRiscv spec)

**Related Files:**
- `rtl/hive/vexriscv_wrapper.sv`
- `rtl/hive/VexRiscv/` (submodule)

---
