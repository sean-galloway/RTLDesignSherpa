# TASK-007: CocoTB Mesh Integration Testbench

> Migrated 2026-09-25 from `projects/components/delta/TASKS.md`
> as **TASK-007** (tooling TOOL-001), ID unchanged. Classified against the
> tree, not its Status line.

**Status:** Planned
**Priority:** P1
**Effort:** 4 days
**Owner:** Unassigned

**Description:**
Create end-to-end mesh network testbench with traffic generation.

**Acceptance Criteria:**
- [ ] Create DeltaMeshTB class
- [ ] Implement AXI master/slave BFMs on all 16 NIs
- [ ] Generate uniform random traffic
- [ ] Generate hotspot traffic patterns
- [ ] Measure network throughput and latency
- [ ] Verify deadlock-free operation
- [ ] Create test_delta_mesh_integration.py

**Dependencies:**
- TASK-005 (Mesh topology implementation)
- TASK-006 (Router testbench)

**Related Files:**
- `val/delta/test_delta_mesh_integration.py`
- `bin/TBClasses/delta/delta_mesh_tb.py`

---
