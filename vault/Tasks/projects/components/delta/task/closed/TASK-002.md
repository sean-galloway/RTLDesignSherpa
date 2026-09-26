# TASK-002: Complete Specification Chapter 5 (Flow Control)

> Migrated 2026-09-25 from `projects/components/delta/TASKS.md`
> as **TASK-002** (tooling TOOL-001), ID unchanged. Classified against the
> tree, not its Status line.


**CLOSED on migration 2026-09-25: the premise was stale, the work is done.**
This asked to "Complete Specification Chapter 5 (Flow Control)" and named
`docs/delta_spec/ch05_flow_control/01_credit_mechanism.md`. That directory does
NOT exist -- ch05 is now `ch05_registers`. Credit-based flow control is
specified at `ch02_blocks/04_virtual_channel_allocator.md:42` (## 4.2
Credit-Based Flow Control) and the credit manager appears in the block overview
at `00_block_overview.md:92`.

**Status:** closed 2026-09-25 (done; the premise was stale -- see below)
**Priority:** P0
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Document credit-based flow control mechanism and backpressure handling.

**Acceptance Criteria:**
- [ ] Define credit counter mechanism
- [ ] Specify buffer management strategy
- [ ] Document backpressure propagation
- [ ] Add flow control timing diagrams
- [ ] Define credit initialization

**Dependencies:**
- Chapter 4 (Routing Algorithm) complete

**Related Files:**
- `docs/delta_spec/ch05_flow_control/01_credit_mechanism.md`

---
