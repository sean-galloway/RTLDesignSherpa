# TASK-017: PlantUML FSM Diagrams

> Migrated 2026-09-25 from `projects/components/hive/TASKS.md`
> as **TASK-017** (tooling TOOL-001), ID unchanged. Classified against the
> tree: hive has ZERO `.sv` files, zero tests, no SERV or VexRiscv source,
> and only `ch01_overview/` plus `ch02_blocks/00_overview.md` written -- so
> every item except TASK-000 is genuinely open, and each item's stated
> Related Files path does not exist yet.

**Status:** Planned
**Priority:** P2
**Effort:** 1 day
**Owner:** Unassigned

**Description:**
Create PlantUML state machine diagrams for HIVE FSMs.

**Acceptance Criteria:**
- [ ] Create mem_arbiter_fsm.puml
- [ ] Create boot_controller_fsm.puml
- [ ] Create serv_state_machine.puml (if applicable)
- [ ] Generate PNG/SVG from all PUML files
- [ ] Place in docs/hive_spec/assets/puml/

**Dependencies:**
- TASK-008 (Memory arbiter) - for accurate FSMs

**Related Files:**
- `docs/hive_spec/assets/puml/*.puml`

---
