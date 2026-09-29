# TASK-035: Make APB Crossbar Variants Functional

> Migrated 2026-09-27 from `vault/Tasks/amba/open.md` as **TASK-022** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P2
**Status:** CLOSED 2026-09-28 (satisfied by the apbx-xbar lane's work; re-measured)
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

---

## CLOSED 2026-09-28 -- satisfied, re-measured rather than taken on trust

This item was written when `apbx_xbar_thin` was the only proven variant and
was filed in amba although the crossbar is a component (its own lane,
`vault/Tasks/projects/components/fabric-gen-ip/apbx-xbar/`). That lane did the work as
TASK-001 (generalize to APB4 / APB5 / mixed), TASK-002 (formal coverage of
the version gating), TASK-003 (APB5 parity across the fabric) and TASK-004
(scrub the tests for completeness), all closed. Checked today against the
tree:

| Deliverable here | State |
|---|---|
| all variants functional | five generated variants (1to1, 2to1, 1to4, 2to4, 2to2_mixed); `dv/tests` GATE from `make clean-all`: 9/9 |
| lint | the five tops lint through `rtl/filelists/apbx_xbar_all.f` with the area's recipe; the only findings are PINCONNECTEMPTY on deliberately unconnected pins, which `rtl/make/area.mk` waives |
| comprehensive tests | one suite per variant plus `test_apbx_xbar_timing.py`; the lane's TASK-004 scrubbed them |
| configuration guide / variant selection | the MAS (`docs/apbx_xbar_mas/`, chapters 01 architecture, 02 address and arbitration, 03 RTL generator) and the HAS, both built to PDF v1.0 |
| integration examples | RLB's `rlb_top` runs the generated 1-to-10 crossbar (RLB/pic_8259 TASK-001 added slave 9) |

"Buffered variants" in the original text referred to the thin/buffered split
of the hand-written crossbar, which no longer exists: every variant is
generated, and the registered response path is the generator's design.
Nothing remained to do in amba.
