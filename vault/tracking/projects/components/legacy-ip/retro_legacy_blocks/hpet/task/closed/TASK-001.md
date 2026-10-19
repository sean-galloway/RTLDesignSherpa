# TASK-001: Timer 2+ not firing in multi-timer tests
> Migrated 2026-09-25 from `projects/components/retro_legacy_blocks/TASKS.md` as **TASK-001** (tooling TOOL-001). That file numbered its own items TASK-001..006, which collide with RLB-001..017 on the frozen legacy page; per-lane IDs replace them. Body preserved as written except the Status line.

**Status:** CLOSED -- fixed 2025-10-17. Verified against the tree 2026-09-25: the
counter cleanup is in `hpet_tests_medium.py` and no `timer 2`/multi-timer defect
reference survives in `test_apb4_hpet.py`. Root cause was test cleanup, not RTL:
the 64-bit counter test left the counter at 0xFFFFFFF0DEADBEEF, so Timer 2
(period 700) never reached its fire condition.

**Description:**
Fixed Timer 2 and higher-numbered timers not firing in multi-timer configurations (3-timer and 8-timer tests). Root cause was simple test cleanup - the 64-bit Counter test was leaving the counter at random values instead of resetting to 0.

**Root Cause:**
The 64-bit Counter test (hpet_tests_medium.py:176-230) writes test values to counter (0xDEADBEEF, 0xFFFFFFF0) but didn't reset counter to 0 at end of test. Subsequent Multiple Timers test started with counter at 0xFFFFFFF0DEADBEEF instead of 0, causing Timer 2 (period=700) to never reach its fire condition.

**Location:**
- File: `dv/tbclasses/hpet/hpet_tests_medium.py`
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
- 3-timer AMD-like (no CDC): 12/12 tests passing (100%)
- All Timer 0, Timer 1, Timer 2 fire correctly
- Test passes reliably with 20µs timeout

**Related Files:**
- Fixed: `dv/tbclasses/hpet/hpet_tests_medium.py`
- Updated: `projects/components/retro_legacy_blocks/docs/IMPLEMENTATION_STATUS.md`
- Documented: `projects/components/retro_legacy_blocks/CLAUDE.md` (Rule #1: Timer Cleanup is MANDATORY)

**Dependencies:** None

**Completion Criteria:**
- Counter cleanup added to test_64bit_counter
- Timeout increased in test_multiple_timers
- 3-timer configuration passing 100%
- Documentation updated

**Notes:**
- The fix was trivial (3 lines changed), but the impact was significant
- This demonstrates the importance of test cleanup between test cases
- The problem was NOT an RTL bug - the RTL was correct all along
- Lesson: Always reset hardware state (counters, configuration) between tests

---
