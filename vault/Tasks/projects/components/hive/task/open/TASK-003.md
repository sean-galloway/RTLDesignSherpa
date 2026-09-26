# TASK-003: Complete Specification Chapter 3 (Memory Subsystem)

> Migrated 2026-09-25 from `projects/components/hive/TASKS.md`
> as **TASK-003** (tooling TOOL-001), ID unchanged. Classified against the
> tree: hive has ZERO `.sv` files, zero tests, no SERV or VexRiscv source,
> and only `ch01_overview/` plus `ch02_blocks/00_overview.md` written -- so
> every item except TASK-000 is genuinely open, and each item's stated
> Related Files path does not exist yet.

**Status:** Planned
**Priority:** P0
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Document the shared memory subsystem including SRAM, ROM, and memory arbitration.

**Acceptance Criteria:**
- [ ] Define shared SRAM architecture (1 VexRiscv + 16 SERV access)
- [ ] Specify memory arbiter design (round-robin, priority)
- [ ] Document ROM configuration and initialization
- [ ] Add memory map and address decoding
- [ ] Include memory timing diagrams

**Dependencies:**
- TASK-001 (SERV spec)
- TASK-002 (VexRiscv spec)

**Related Files:**
- `docs/hive_spec/ch03_memory/01_memory_subsystem.md`

---
