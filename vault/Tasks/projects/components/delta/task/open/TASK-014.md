# TASK-014: Larger Mesh Topologies

> Migrated 2026-09-25 from `projects/components/delta/TASKS.md`
> as **TASK-014** (tooling TOOL-001), ID unchanged. Classified against the
> tree, not its Status line.

**Priority:** P3
**Description:** Parameterize mesh size beyond 4×4 (e.g., 8×8, 16×16).

> **Scope tension, recorded not resolved (2026-09-25).** This item assumes a
> 4x4 MESH. `PRD.md` commits Delta to TWO topologies -- flat crossbar and tree
> (`REQ-GEN-002`, sections 2.1/2.2, `--topology both`) -- and says nothing about a
> mesh. The spec still specifies mesh routers, so the item is kept OPEN rather
> than dropped, but whether mesh is in scope is the owner's call.
