# reset_sync - Known RTL Issues

## ✅ RESOLVED: Inverted Reset Polarity in Always Block

**Severity**: High
**Impact**: Reset synchronizer non-functional - output stuck low
**Status**: ✅ FIXED
**Discovery Date**: 2025-10-14
**Resolution Date**: 2025-10-14

### Description

The reset synchronizer module `reset_sync.sv` had inverted reset polarity logic in the synchronization always block. The condition checked `if (rst_n)` instead of `if (!rst_n)`, causing the synchronizer to be stuck in reset state when reset was deasserted.

### Location

**File**: `rtl/common/reset_sync.sv`
**Line**: 16

### Original Code (Problematic)

```systemverilog
// WRONG: Inverted reset polarity logic
always_ff @(posedge clk or negedge rst_n) begin
    if (rst_n) begin  // ❌ WRONG: This checks if reset is HIGH (not asserted)
        sync_chain <= '0;
    end else begin
        sync_chain <= {sync_chain[N-2:0], async_rst_in};
    end
end
```

### Impact on Functionality

1. **Reset stuck active** - Synchronizer output remained low even after reset deassertion
2. **No synchronization** - Asynchronous reset never propagated through chain
3. **Downstream blocks stuck** - Any logic relying on synchronized reset was held in reset
4. **Test failures** - All reset propagation tests failed

### Root Cause

**Logic Error**: Asynchronous reset blocks require `if (!rst_n)` for active-low reset convention.

**What happened:**
- `rst_n = 0` (reset asserted) → Condition `if (rst_n)` is FALSE → Goes to `else` branch → Tries to shift chain
- `rst_n = 1` (reset deasserted) → Condition `if (rst_n)` is TRUE → Sets chain to 0 → Output stuck low

**Should have been:**
- `rst_n = 0` (reset asserted) → Condition `if (!rst_n)` is TRUE → Sets chain to 0 ✅
- `rst_n = 1` (reset deasserted) → Condition `if (!rst_n)` is FALSE → Shifts chain ✅

### Fix Applied

```systemverilog
// ✅ FIXED: Correct active-low reset polarity
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin  // ✅ CORRECT: Active-low reset check
        sync_chain <= '0;
    end else begin
        sync_chain <= {sync_chain[N-2:0], async_rst_in};
    end
end
```

**Change**: Line 16 changed from `if (rst_n)` to `if (!rst_n)`

### Verification

**Test Created**: `val/common/test_reset_sync.py`

**Test Coverage:**
1. ✅ Basic synchronization (4 test configs: N=2,3,4,5)
2. ✅ Immediate reset assertion behavior
3. ✅ Multiple cycle reset hold
4. ✅ Glitch filtering on async input

**Results:**
```bash
$ pytest val/common/test_reset_sync.py -v
test_reset_sync.py::test_reset_sync[2-min]      PASSED
test_reset_sync.py::test_reset_sync[3-typical]  PASSED
test_reset_sync.py::test_reset_sync[4-safe]     PASSED
test_reset_sync.py::test_reset_sync[5-max]      PASSED
======================== 4 passed in 1.15s ========================
```

**Verification Steps:**
1. ✅ Applied fix to `reset_sync.sv:16`
2. ✅ Created comprehensive test suite
3. ✅ All 4 test configurations passing
4. ✅ Verified synchronizer chain progresses correctly
5. ✅ Verified proper glitch filtering (N clock cycles)
6. ✅ Updated documentation in `docs/markdown/RTLCommon/reset_sync.md`

### Related Files

- ✅ `rtl/common/reset_sync.sv` (fix applied line 16)
- ✅ `val/common/test_reset_sync.py` (new test file created)
- ✅ `bin/CocoTBFramework/tbclasses/reset_sync_tb.py` (new testbench class)
- ✅ `docs/markdown/RTLCommon/reset_sync.md` (updated)
- ✅ `rtl/common/TASKS.md` (task completed, progress tracked)

### Lessons Learned

1. **Reset polarity is critical** - Active-low reset requires `if (!rst_n)`, not `if (rst_n)`
2. **Test-driven debugging** - Creating comprehensive test revealed the bug immediately
3. **Asynchronous reset conventions** - Always double-check reset sensitivity and polarity
4. **Simulation validates logic** - Bug would have been caught earlier with basic simulation

### Prevention

**Code Review Checklist:**
- ✅ Asynchronous reset blocks use `if (!rst_n)` for active-low convention
- ✅ Sensitivity list includes `negedge rst_n` for active-low async reset
- ✅ Reset behavior validated with comprehensive tests
- ✅ All reset synchronizers tested for proper propagation

---

**Fixed By**: Claude Code (AI Assistant)
**Verification**: pytest test suite
**Commit**: ec6f36e (2025-10-14)
**Status**: ✅ Production-Ready - All tests passing
