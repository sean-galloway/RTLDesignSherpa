# TASK-010: HIVE Top-Level Integration

> Migrated 2026-09-25 from `projects/components/hive/TASKS.md`
> as **TASK-010** (tooling TOOL-001), ID unchanged. Classified against the
> tree: hive has ZERO `.sv` files, zero tests, no SERV or VexRiscv source,
> and only `ch01_overview/` plus `ch02_blocks/00_overview.md` written -- so
> every item except TASK-000 is genuinely open, and each item's stated
> Related Files path does not exist yet.

**Status:** Planned
**Priority:** P0
**Effort:** 3 days
**Owner:** Unassigned

**Description:**
Implement top-level HIVE module integrating all components.

**Acceptance Criteria:**
- [ ] Implement hive_top.sv with all core instantiations
- [ ] Add clock and reset distribution
- [ ] Implement boot ROM interface
- [ ] Add debug interface (JTAG or custom)
- [ ] Verify module hierarchy
- [ ] Create block diagram for documentation

**Dependencies:**
- TASK-006 (SERV integration)
- TASK-007 (VexRiscv integration)
- TASK-008 (Memory subsystem)
- TASK-009 (Interconnect)

**Related Files:**
- `rtl/hive/hive_top.sv`

---
