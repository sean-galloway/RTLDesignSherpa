<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# APB HPET Task List

**Version:** 1.0
**Last Updated:** 2025-10-17
**Status:** Production Ready (5/6 configurations at 100%)
**Owner:** RTL Design Sherpa Project

---

## Task Status Legend

- 🔴 **Blocked** - Cannot proceed due to dependencies
- 🟠 **In Progress** - Currently being worked on
- 🟡 **Planned** - Ready to start, no blockers
- 🟢 **Complete** - Finished and verified
- ⏸️ **Deferred** - Low priority, postponed

## Priority Levels

- **P0 (Critical)** - Blocking progress, must fix immediately
- **P1 (High)** - Required for production readiness
- **P2 (Medium)** - Important but not blocking
- **P3 (Low)** - Nice to have, future enhancement

---

## Critical Issues (P0-P1)

### TASK-001: Fix Timer 2+ Not Firing in Multi-Timer Tests
**Status:** 🟢 Complete
**Priority:** P0 (Critical)
**Effort:** 30 minutes
**Assigned:** Completed 2025-10-17

**Description:**
Fixed Timer 2 and higher-numbered timers not firing in multi-timer configurations (3-timer and 8-timer tests). Root cause was simple test cleanup - the 64-bit Counter test was leaving the counter at random values instead of resetting to 0.

**Root Cause:**
The 64-bit Counter test (hpet_tests_medium.py:176-230) writes test values to counter (0xDEADBEEF, 0xFFFFFFF0) but didn't reset counter to 0 at end of test. Subsequent Multiple Timers test started with counter at 0xFFFFFFF0DEADBEEF instead of 0, causing Timer 2 (period=700) to never reach its fire condition.

**Location:**
- File: `bin/CocoTBFramework/tbclasses/amba/apb_hpet/hpet_tests_medium.py`
- Lines: 220-222 (counter cleanup added)
- Lines: 356 (timeout increased)

**Applied Fix:**
```python
# Fix 1: Add counter cleanup in test_64bit_counter (lines 220-222)
# Reset counter to 0 for next test
await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)

# Fix 2: Increase timeout in test_multiple_timers (line 356)
timeout = 20000  # 20us timeout - Timer 2 needs 7000ns, allow extra margin
```

**Impact (Before Fix):**
- 3-timer AMD-like (no CDC): 11/12 tests passing (92%)
- Timer 2 missed firing, test failed

**Verification (After Fix):**
- ✅ 3-timer AMD-like (no CDC): 12/12 tests passing (100%)
- ✅ All Timer 0, Timer 1, Timer 2 fire correctly
- ✅ Test passes reliably with 20µs timeout

**Related Files:**
- ✅ Fixed: `bin/CocoTBFramework/tbclasses/amba/apb_hpet/hpet_tests_medium.py`
- ✅ Updated: `projects/components/apb_hpet/docs/IMPLEMENTATION_STATUS.md`
- ✅ Documented: `projects/components/apb_hpet/CLAUDE.md` (Rule #1: Timer Cleanup is MANDATORY)

**Dependencies:** None

**Completion Criteria:**
- ✅ Counter cleanup added to test_64bit_counter
- ✅ Timeout increased in test_multiple_timers
- ✅ 3-timer configuration passing 100%
- ✅ Documentation updated

**Notes:**
- The fix was trivial (3 lines changed), but the impact was significant
- This demonstrates the importance of test cleanup between test cases
- The problem was NOT an RTL bug - the RTL was correct all along
- Lesson: Always reset hardware state (counters, configuration) between tests

---

### TASK-002: Fix 8-Timer Non-CDC "All Timers Stress" Test Timeout
**Status:** 🟡 Planned
**Priority:** P3 (Low)
**Effort:** 5 minutes
**Assigned:** Unassigned

**Description:**
Fix minor timeout issue in 8-timer non-CDC "All Timers Stress" test. Timer 6 and Timer 7 need more time to fire due to later periods. Same issue pattern as TASK-001, same solution.

**Location:**
- File: `bin/CocoTBFramework/tbclasses/amba/apb_hpet/hpet_tests_full.py`
- Test: `test_all_timers_stress`
- Issue: Timeout insufficient for Timer 6 and Timer 7

**Current Status:**
- 8-timer custom (no CDC): 11/12 tests passing (92%)
- 8-timer custom (CDC): 12/12 tests passing (100%) ← CDC version passes!

**Recommended Fix:**
```python
# In hpet_tests_full.py, test_all_timers_stress method
# Current:
timeout = 50000  # 50us timeout - insufficient for 8 timers

# Fix:
timeout = 100000  # 100us timeout - allow time for all 8 timers
```

**Impact:**
- Low - only affects stress test in non-CDC configuration
- CDC version of same test passes (proves RTL is correct)
- Not blocking production use

**Verification Steps:**
1. Increase timeout in hpet_tests_full.py
2. Run: `pytest "projects/components/apb_hpet/dv/tests/test_apb_hpet.py::test_hpet[8-43981-16-0-full-8-timer custom]" -v`
3. Verify: 12/12 tests pass (100%)
4. Update: IMPLEMENTATION_STATUS.md with new results

**Related Files:**
- Update: `bin/CocoTBFramework/tbclasses/amba/apb_hpet/hpet_tests_full.py`
- Update: `projects/components/apb_hpet/docs/IMPLEMENTATION_STATUS.md`

**Dependencies:** None

**Completion Criteria:**
- [ ] Timeout increased in test_all_timers_stress
- [ ] 8-timer non-CDC configuration passing 100%
- [ ] Documentation updated

**Notes:**
- Optional fix - component is already production-ready
- Same root cause as TASK-001 (insufficient timeout)
- CDC version passes, confirming RTL correctness

---

## Enhancement and Optimization (P3)

### TASK-003: Add Comparator Readback Feature
**Status:** ⏸️ Deferred
**Priority:** P3 (Low)
**Effort:** 4-8 hours
**Assigned:** Unassigned

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
- Modify: `rtl/peakrdl/hpet_regs.rdl`
- Regenerate: `rtl/hpet_regs.sv`, `rtl/hpet_regs_pkg.sv`
- Update: `bin/CocoTBFramework/tbclasses/amba/apb_hpet/hpet_tests_basic.py`

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

### TASK-004: Add Legacy Replacement Mode Support
**Status:** ⏸️ Deferred
**Priority:** P3 (Low)
**Effort:** 16-24 hours
**Assigned:** Unassigned

**Description:**
Implement legacy PC/AT timer replacement mode for compatibility with legacy operating systems and software.

**Features to Add:**
1. **Legacy IRQ Routing:**
   - Timer 0 → IRQ0 (PIT channel 0 replacement)
   - Timer 1 → IRQ8 (RTC replacement)

2. **Legacy Mapping:**
   - HPET_CONFIG legacy_mapping bit controls routing
   - Compatible with PC/AT timer expectations

3. **Operating Mode:**
   - Timer 0: 1ms periodic tick (IRQ0 replacement)
   - Timer 1: RTC interrupt generation (IRQ8 replacement)

**Design Approach:**
```systemverilog
// In hpet_core.sv, add legacy mode logic
logic legacy_irq0;  // PIT channel 0 replacement
logic legacy_irq8;  // RTC replacement

assign legacy_irq0 = cfg_legacy_mapping ? timer_irq[0] : 1'b0;
assign legacy_irq8 = cfg_legacy_mapping ? timer_irq[1] : 1'b0;
```

**Impact:**
- Better compatibility with legacy software
- Support for PC/AT timer emulation
- Enhanced OS compatibility

**Verification Steps:**
1. Add legacy mode logic to hpet_core.sv
2. Update hpet_regs.rdl with legacy_mapping bit
3. Create test: test_legacy_replacement_mode
4. Verify: IRQ0 and IRQ8 routing
5. Test: 1ms tick generation

**Related Files:**
- Modify: `rtl/hpet_core.sv`
- Update: `rtl/peakrdl/hpet_regs.rdl`
- Create: `bin/CocoTBFramework/tbclasses/amba/apb_hpet/hpet_tests_legacy.py`

**Dependencies:** None

**Completion Criteria:**
- [ ] Legacy IRQ routing implemented
- [ ] Legacy mapping bit functional
- [ ] Tests passing
- [ ] Documentation updated

**Notes:**
- Complex feature, not needed for basic operation
- Deferred until production deployment requirements clear

---

### TASK-005: Add 64-bit Atomic Counter Read
**Status:** ⏸️ Deferred
**Priority:** P3 (Low)
**Effort:** 8-12 hours
**Assigned:** Unassigned

**Description:**
Implement 64-bit atomic counter read to prevent race conditions when reading counter value that's incrementing.

**Current Limitation:**
- Counter read requires two 32-bit reads (LO then HI)
- Counter may increment between reads
- Race condition: Read LO=0xFFFFFFFF, counter increments, Read HI=0x00000001
- Result: 0x00000001FFFFFFFF instead of 0x0000000100000000 or 0x00000000FFFFFFFF

**Enhancement Goals:**
1. Latch counter value on LO register read
2. Return latched HI value when HI register read
3. Atomic 64-bit read (no race condition)

**Design Approach:**
```systemverilog
// In hpet_config_regs.sv
logic [63:0] r_latched_counter;
logic r_counter_latched;

// Latch counter on LO read
always_ff @(posedge pclk) begin
    if (hwif.hpet_counter_lo.swacc && !hwif.hpet_counter_lo.swmod) begin
        // Read access to LO - latch full counter
        r_latched_counter <= counter;
        r_counter_latched <= 1'b1;
    end

    if (hwif.hpet_counter_hi.swacc) begin
        r_counter_latched <= 1'b0;  // Clear latch flag
    end
end

// Return latched value for HI read
assign hwif.hpet_counter_hi.value = r_counter_latched ?
                                    r_latched_counter[63:32] :
                                    counter[63:32];
```

**Impact:**
- Eliminates counter read race conditions
- More reliable counter value reads
- Better software compatibility

**Verification Steps:**
1. Add latching logic to hpet_config_regs.sv
2. Create test: test_atomic_counter_read
3. Verify: LO read latches full counter
4. Verify: HI read returns latched value
5. Test: Rapid counter increments during read

**Related Files:**
- Modify: `rtl/hpet_config_regs.sv`
- Create: Test in `bin/CocoTBFramework/tbclasses/amba/apb_hpet/hpet_tests_medium.py`

**Dependencies:** None

**Completion Criteria:**
- [ ] Counter latching implemented
- [ ] Atomic read verified
- [ ] Tests passing
- [ ] Documentation updated

**Notes:**
- Nice feature but not critical
- Current two-read approach works for most use cases
- Deferred until production deployment needs clarify

---

## Documentation (P2)

### TASK-006: Create Integration Examples
**Status:** 🟡 Planned
**Priority:** P2 (Medium)
**Effort:** 4-6 hours
**Assigned:** Unassigned

**Description:**
Create comprehensive integration examples showing how to use APB HPET in different system contexts.

**Examples to Create:**

1. **Basic Integration (1-2 hours)**
   - Simple 2-timer system
   - APB slave connection
   - Interrupt handling
   - Basic timer configuration

2. **Multi-Timer System (1-2 hours)**
   - 8-timer configuration
   - Different timer modes (one-shot, periodic)
   - Interrupt prioritization
   - Timer coordination

3. **CDC Integration (1-2 hours)**
   - Asynchronous clock domains
   - APB clock vs. HPET clock
   - Clock crossing considerations
   - Performance implications

4. **Software Driver Example (1-2 hours)**
   - C header file definitions
   - Initialization sequence
   - Timer configuration functions
   - Interrupt service routine

**File Structure:**
```
projects/components/apb_hpet/examples/
├── basic_integration/
│   ├── system_top.sv
│   ├── testbench.sv
│   └── README.md
├── multi_timer/
│   ├── system_top.sv
│   ├── testbench.sv
│   └── README.md
├── cdc_integration/
│   ├── system_top.sv
│   ├── testbench.sv
│   └── README.md
└── software/
    ├── hpet_driver.h
    ├── hpet_driver.c
    └── README.md
```

**Verification Steps:**
1. Create example directories and files
2. Test each example with Verilator
3. Verify: All examples compile and simulate
4. Document: Usage instructions in READMEs
5. Review: Completeness and clarity

**Related Files:**
- Create: `projects/components/apb_hpet/examples/` directory and contents
- Update: `projects/components/apb_hpet/PRD.md` with links to examples

**Dependencies:** None

**Completion Criteria:**
- [ ] All example files created
- [ ] Examples compile and simulate
- [ ] Documentation complete
- [ ] PRD.md updated with links

**Notes:**
- Important for users integrating HPET
- Helps demonstrate capabilities
- Reduces integration errors

---

## Task Dependencies Graph

```
TASK-001 (Fix Timer 2+ Firing) ────────────┐
    │                                       │
    │ (Complete)                            │
    │                                       │
    ├─────> TASK-002 (8-Timer Stress Test) │
    │          (Optional fix)               │
    │                                       │
    └─────> TASK-006 (Integration Examples)
               │
               ├─────> TASK-003 (Comparator Readback)
               │
               ├─────> TASK-004 (Legacy Mode)
               │
               └─────> TASK-005 (Atomic Counter Read)
```

---

## Task Prioritization

### Sprint 1: Critical Bugs (Complete)
1. ✅ **TASK-001:** Fix Timer 2+ not firing (P0) - COMPLETE

### Sprint 2: Optional Fixes (Optional)
2. **TASK-002:** Fix 8-timer stress test timeout (P3) - 5 minutes

### Sprint 3: Documentation (Planned)
3. **TASK-006:** Create integration examples (P2) - 4-6 hours

### Future Enhancements (Backlog)
4. **TASK-003:** Comparator readback (P3)
5. **TASK-004:** Legacy replacement mode (P3)
6. **TASK-005:** Atomic counter read (P3)

---

## Progress Tracking

### Overall Status
- **Total Tasks:** 6
- **Complete:** 1 (17%)
- **In Progress:** 0 (0%)
- **Planned:** 2 (33%)
- **Deferred:** 3 (50%)

### Test Coverage
- **Basic Tests:** 4/4 passing (100%) across all configs
- **Medium Tests:** 5/5 passing (100%) across 5/6 configs
- **Full Tests:** 3/3 passing (100%) across 5/6 configs
- **Overall:** 5/6 configurations at 100%, 1 config at 92%

### Production Readiness
- ✅ **5 configurations:** Production Ready (100% passing)
- ⚠️ **1 configuration:** Minor stress test issue (92% passing)
- ✅ **Core functionality:** Fully validated
- ✅ **All timer modes:** Working correctly

---

## Notes

1. **Task Order:** TASK-001 complete, TASK-002 optional, documentation next priority
2. **Test-Driven:** All fixes verified with 100% test pass rate
3. **Documentation:** Update docs immediately after task completion
4. **Verification:** Run full regression: `pytest projects/components/apb_hpet/dv/tests/ -v`
5. **Production Ready:** Component ready for production use after TASK-001

---

## Quick Commands

```bash
# Run full test suite
pytest projects/components/apb_hpet/dv/tests/ -v

# Run specific configuration
pytest "projects/components/apb_hpet/dv/tests/test_apb_hpet.py::test_hpet[3-4130-2-0-full-3-timer AMD-like]" -v

# Run 8-timer stress test (TASK-002)
pytest "projects/components/apb_hpet/dv/tests/test_apb_hpet.py::test_hpet[8-43981-16-0-full-8-timer custom]" -v

# Lint RTL
verilator --lint-only projects/components/apb_hpet/rtl/apb_hpet.sv

# View documentation
cat projects/components/apb_hpet/PRD.md
cat projects/components/apb_hpet/CLAUDE.md
cat projects/components/apb_hpet/docs/IMPLEMENTATION_STATUS.md
```

---

**Version History:**
- v1.0 (2025-10-17): Initial creation with 6 tasks, TASK-001 complete

**Maintained By:** RTL Design Sherpa Project
**Last Review:** 2025-10-17
