# TASK-002: comparator registers are write-only
> Migrated 2026-09-25 from `projects/components/retro_legacy_blocks/TASKS.md` as **TASK-003** (tooling TOOL-001). That file numbered its own items TASK-001..006, which collide with RLB-001..017 on the frozen legacy page; per-lane IDs replace them. Body preserved as written except the Status line.

**Priority:** P3
**Status:** open. Confirmed against the RTL 2026-09-25: zero hits for
`comparator_readback` under `retro_legacy_blocks/rtl/`, so nothing of this is built.
**Owner:** TBD

**Description:**
Add read access to timer comparator registers. Currently comparators are write-only, preventing software from reading current comparator values.

**Current Limitation:**
- TIMER_COMPARATOR_LO/HI registers are write-only
- Software cannot read back programmed comparator values
- Debugging and diagnostics more difficult

**Enhancement Goals:**
1. Make comparator registers read/write instead of write-only
2. Return current comparator value on read
3. Support both one-shot and periodic modes
4. Maintain existing write behavior

**Design Approach:**
```systemverilog
// In hpet_regs.rdl, update comparator field properties
field comparator_lo {
    sw = rw;  // Change from sw=w to sw=rw
    hw = r;   // Hardware can read
};
```

**Impact:**
- Improved software debugging capabilities
- Better diagnostic features
- Enhanced HPET monitoring

**Verification Steps:**
1. Update hpet_regs.rdl SystemRDL specification
2. Regenerate registers: `peakrdl regblock hpet_regs.rdl --cpuif apb4`
3. Add readback test to hpet_tests_basic.py
4. Verify: Write comparator, read back, values match
5. Test: Both one-shot and periodic modes

**Related Files:**
- Modify: `rdl/hpet/hpet_regs.rdl`
- Regenerate: `rtl/hpet/hpet_regs.sv`, `rtl/hpet/hpet_regs_pkg.sv`
- Update: `dv/tbclasses/hpet/hpet_tests_basic.py`

**Dependencies:** None

**Completion Criteria:**
- [ ] Comparator registers support read access
- [ ] Read returns current comparator value
- [ ] Tests passing
- [ ] Documentation updated

**Notes:**
- Nice to have, not critical for operation
- Deferred until core functionality stable

---
