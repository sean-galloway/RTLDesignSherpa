# AXI Monitor Known Issues

This directory tracks known bugs and issues in the AXI monitor subsystem.

---

## Active Issues

### ✅ ALL ISSUES RESOLVED

---

## Resolved Issues

### ✅ FIXED (2025-10-03)

#### Issue #1: Orphan Error Packet Flood
**File:** `axi_monitor_orphan_error_flood.md`
**Status:** ✅ FIXED (2025-10-03)
**Severity:** HIGH - Blocks monitor operation

**Summary:** Monitor generated continuous duplicate error packets after detecting orphan data, flooding the monitor bus and blocking legitimate completion packets.

**Impact (Before Fix):**
- 4/11 tests failing (all ID_WIDTH=8 configurations)
- Monitor bus saturation
- Unable to track transaction completions during stress tests

**Fix Applied:**
- **File:** `rtl/amba/shared/axi_monitor_reporter.sv`
- **Change:** Added `TRANS_ORPHANED` state to `w_events_to_mark` logic
- **Result:** All 11/11 tests now passing

**Quick Reference:**
- **Affected module:** `axi_monitor_reporter.sv`
- **Root cause:** Orphan error flag not cleared after packet generation (TRANS_ORPHANED state excluded from event marking logic)
- **Fix:** Include TRANS_ORPHANED in event_reported flag update logic

---

### ✅ RESOLVED (2025-09-30)

#### Issue #0: Event Reported Feedback Bug
**File:** `axi_monitor_reporter.md`
**Status:** ✅ FIXED (2025-09-30)
**Severity:** MEDIUM

**Summary:** Transaction table entries weren't cleared after error events were reported, causing table exhaustion.

**Fix:** Added `event_reported_flags` feedback from reporter to trans_mgr to properly clear table entries after event reporting.

---

## Test Status Summary

**Overall:** 11/11 tests passing (100%) ✅

### All Tests Passing (11/11)
- ✅ `[4-32-8-True-True-protocol]` - AXI4 Read
- ✅ `[4-32-8-False-True-protocol]` - AXI4 Write
- ✅ `[4-32-8-True-False-protocol]` - AXI4-Lite Read
- ✅ `[4-32-8-False-False-protocol]` - AXI4-Lite Write
- ✅ `[4-32-2-True-True-table]` - Small table size (2 slots)
- ✅ `[4-32-16-True-True-table]` - Large table size (16 slots)
- ✅ `[4-64-8-True-True-addr64]` - 64-bit addressing
- ✅ `[8-32-8-True-True-id_space]` - 256 IDs, 8 slots (FIXED)
- ✅ `[8-32-16-True-True-id_space]` - 256 IDs, 16 slots (FIXED)
- ✅ `[8-64-8-True-True-addr64]` - 64-bit addr, 8-bit ID (FIXED)
- ✅ `[8-64-16-True-True-combined]` - Combined stress (FIXED)

**Status:** All tests passing after orphan flood fix (2025-10-03)

---

## Bug Reporting

When reporting new issues, please include:

1. **Configuration** - Parameter values (ID_WIDTH, ADDR_WIDTH, MAX_TRANSACTIONS, etc.)
2. **Test case** - Reproducible test sequence
3. **Expected vs Actual** - What should happen vs what actually happens
4. **Log files** - Relevant excerpts from simulation logs
5. **Time window** - Simulation time or line numbers where issue occurs
6. **Waveform** - If available, point to specific signals/times

---

## Investigation Tools

### Finding Issues in Logs
```bash
# Find test failures
grep "FAIL" val/amba/logs/*.log

# Find duplicate packets
grep "UNKNOWN_EVENT_2" val/amba/logs/*.log | uniq -c

# Check packet counts
grep -c "PktType" val/amba/logs/*.log
```

### Searching RTL
```bash
# Find orphan detection
grep -rn "orphan" rtl/amba/shared/

# Find error generation
grep -rn "UNKNOWN_EVENT" rtl/amba/shared/

# Check event feedback
grep -rn "event_reported" rtl/amba/shared/
```

---

## Version History

| Date       | Event |
|------------|-------|
| 2025-10-03 | Issue #1 FIXED - Orphan error flood resolved, all 11/11 tests passing |
| 2025-10-02 | Issue #1 discovered and documented (orphan error flood) |
| 2025-09-30 | Issue #0 fixed (event reported feedback) |

---

**Maintained by:** RTL Design Sherpa Project
**Last Updated:** 2025-10-03
