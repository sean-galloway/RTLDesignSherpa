# TASK-016: Wavedrom Timing Diagrams

> Migrated 2026-09-25 from `projects/components/hive/TASKS.md`
> as **TASK-016** (tooling TOOL-001), ID unchanged. Classified against the
> tree: hive has ZERO `.sv` files, zero tests, no SERV or VexRiscv source,
> and only `ch01_overview/` plus `ch02_blocks/00_overview.md` written -- so
> every item except TASK-000 is genuinely open, and each item's stated
> Related Files path does not exist yet.

**Status:** Planned
**Priority:** P2
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Create wavedrom JSON files illustrating key HIVE operations.

**Acceptance Criteria:**
- [ ] Create serv_bit_serial_execution.json (SERV bit-serial ADD)
- [ ] Create vexriscv_pipeline.json (VexRiscv 5-stage pipeline)
- [ ] Create mem_arbiter_priority.json (VexRiscv priority access)
- [ ] Create mem_arbiter_round_robin.json (SERV round-robin)
- [ ] Create boot_sequence.json (VexRiscv boot → SERV init)
- [ ] Generate SVG/PNG from all JSON files
- [ ] Place in docs/hive_spec/assets/waves/

**Dependencies:**
- None (can start anytime)

**Related Files:**
- `docs/hive_spec/assets/waves/*.json`

---
