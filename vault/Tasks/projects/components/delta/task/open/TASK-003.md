# TASK-003: Router RTL Implementation

> Migrated 2026-09-25 from `projects/components/delta/TASKS.md`
> as **TASK-003** (tooling TOOL-001), ID unchanged. Classified against the
> tree, not its Status line.

**Status:** Planned
**Priority:** P0
**Effort:** 1 week
**Owner:** Unassigned

**Description:**
Implement the Delta router RTL with input buffers, route computation, virtual channel allocation, and crossbar switch.

**Acceptance Criteria:**
- [ ] Implement router_input_unit.sv (input buffering + route computation)
- [ ] Implement router_vc_allocator.sv (virtual channel allocation)
- [ ] Implement router_switch_allocator.sv (crossbar arbitration)
- [ ] Implement router_crossbar.sv (5×5 crossbar switch)
- [ ] Implement delta_router.sv (top-level integration)
- [ ] Add comprehensive inline comments
- [ ] Verify synthesizability with Verilator

**Dependencies:**
- TASK-001 (Routing Algorithm spec)
- TASK-002 (Flow Control spec)

**Related Files:**
- `rtl/delta/delta_router.sv`
- `rtl/delta/router_input_unit.sv`
- `rtl/delta/router_vc_allocator.sv`
- `rtl/delta/router_switch_allocator.sv`
- `rtl/delta/router_crossbar.sv`

---
