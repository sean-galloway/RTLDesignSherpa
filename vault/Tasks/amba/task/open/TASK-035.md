# TASK-035: Make APB Crossbar Variants Functional

> Migrated 2026-09-27 from `vault/Tasks/amba/open.md` as **TASK-022** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P2
**Status:** Not Started
**Owner:** TBD
**Effort:** Medium (2-3 days)
**Dependencies:** None

**Objective:** Get all APB crossbar variants working and tested

**Background (STALE — see note):** written when `apbx_xbar_thin` was the
only proven variant. As of 2026-08-27 all five generated variants
(1to1/2to1/1to4/2to4/2to2_mixed) pass 8/8 and lint clean, and thin has
been deleted. **This task looks complete; it needs closing or rescoping
rather than doing.**

**Requirements:**

2. **Fix/Verify Buffered Variants**
   - Test apbx_xbar with buffering enabled
   - Identify and fix any issues
   - Verify backpressure handling

3. **Full Feature Testing**
   - Multiple masters × multiple slaves
   - Concurrent transactions
   - Address decoding
   - Error responses

4. **Documentation**
   - Document working variants
   - Configuration guidelines
   - Performance characteristics

**Deliverables:**
- [ ] All APB crossbar variants functional
- [ ] Comprehensive test coverage
- [ ] Configuration guide for variant selection
- [ ] Integration examples updated

**Success Criteria:**
- All APB crossbar tests passing
- Documented working configurations
- Clear guidance on variant selection

---
