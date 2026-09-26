# TASK-005: Mesh Topology RTL Implementation

> Migrated 2026-09-25 from `projects/components/delta/TASKS.md`
> as **TASK-005** (tooling TOOL-001), ID unchanged. Classified against the
> tree, not its Status line.

**Status:** Planned
**Priority:** P0
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Implement the 4×4 mesh topology with router and network interface instantiation.

**Acceptance Criteria:**
- [ ] Implement delta_mesh_4x4.sv with 16 routers + 16 NIs
- [ ] Add parameterization for mesh dimensions
- [ ] Implement proper router-to-router connections
- [ ] Add X-Y coordinate assignment logic
- [ ] Verify all interconnections

**Dependencies:**
- TASK-003 (Router implementation)
- TASK-004 (Network interface implementation)

**Related Files:**
- `rtl/delta/delta_mesh_4x4.sv`

---

> **Scope tension, recorded not resolved (2026-09-25).** This item assumes a
> 4x4 MESH. `PRD.md` commits Delta to TWO topologies -- flat crossbar and tree
> (`REQ-GEN-002`, sections 2.1/2.2, `--topology both`) -- and says nothing about a
> mesh. The spec still specifies mesh routers, so the item is kept OPEN rather
> than dropped, but whether mesh is in scope is the owner's call.
