# TASK-006: CocoTB Router Testbench

> Migrated 2026-09-25 from `projects/components/delta/TASKS.md`
> as **TASK-006** (tooling TOOL-001), ID unchanged. Classified against the
> tree, not its Status line.

**Status:** Planned
**Priority:** P1
**Effort:** 3 days
**Owner:** Unassigned

**Description:**
Create comprehensive CocoTB testbench for single router testing.

**Acceptance Criteria:**
- [ ] Create DeltaRouterTB class in bin/TBClasses/delta/
- [ ] Implement packet injection on all 5 ports
- [ ] Test X-Y routing decisions
- [ ] Verify virtual channel allocation
- [ ] Test credit-based flow control
- [ ] Measure router latency
- [ ] Create test_delta_router.py with >90% coverage

**Dependencies:**
- TASK-003 (Router implementation)

**Related Files:**
- `val/delta/test_delta_router.py`
- `bin/TBClasses/delta/delta_router_tb.py`

---
