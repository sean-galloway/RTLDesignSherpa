# TASK-015: Software Toolchain Setup

> Migrated 2026-09-25 from `projects/components/hive/TASKS.md`
> as **TASK-015** (tooling TOOL-001), ID unchanged. Classified against the
> tree: hive has ZERO `.sv` files, zero tests, no SERV or VexRiscv source,
> and only `ch01_overview/` plus `ch02_blocks/00_overview.md` written -- so
> every item except TASK-000 is genuinely open, and each item's stated
> Related Files path does not exist yet.

**Status:** Planned
**Priority:** P1
**Effort:** 3 days
**Owner:** Unassigned

**Description:**
Set up RISC-V GCC toolchain and example programs for HIVE testing.

**Acceptance Criteria:**
- [ ] Install RISC-V GCC (riscv32-unknown-elf)
- [ ] Create linker script for HIVE memory map
- [ ] Write simple test programs (hello world, task dispatch)
- [ ] Create Makefile for building SERV and VexRiscv binaries
- [ ] Document toolchain setup in CLAUDE.md

**Dependencies:**
- TASK-010 (HIVE top-level) - for memory map

**Related Files:**
- `sw/hive/linker.ld`
- `sw/hive/Makefile`
- `sw/hive/examples/hello_world.c`

---
