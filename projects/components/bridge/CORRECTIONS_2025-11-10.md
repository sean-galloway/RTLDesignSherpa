# Bridge Test Corrections - 2025-11-10

## Summary of Corrections

Based on user feedback, corrected the initial fixes with proper requirements:

1. ✅ **GAXI timeout: 200 cycles** (not 1000 or 10000)
2. ✅ **Soft failure on timeout** - Raises TestFailure for clean VCD exit
3. ✅ **Parallel execution ENABLED** - Test names are unique, no conflicts
4. ✅ **Memory limit: 32GB** - Handles Verilator memory usage properly
5. ℹ️  **APB clock (pclk)** - Not needed in bridge (synchronous crossbar, APB peripheral is external)

---

## Corrected Settings

### 1. GAXI Timeout: 200 Cycles ✅

**User Requirement:**
> "The timeout of 1000 cycles is too long already, assuming the BFMs have reasonable delays."
> "the gaxi timeout for these tests should be 200."

**Implementation:**
```python
# All bridge testbenches now use:
self.ar_m0 = GAXIMaster(
    ...
    timeout_cycles=200,  # Bridge routing delay
    log=self.log
)
```

**Rationale:**
- Bridge crossbar routing is fast with reasonable BFM delays
- 200 cycles is sufficient for address decode + routing
- Catches hanging transactions quickly without excessive wait

**Files Modified:**
- All 12 bridge testbench files
- 72 GAXIMaster instances total

---

### 2. Soft Failure on Timeout ✅

**User Requirement:**
> "If there is one timeout, a soft failure should be set and the simulation exited ASAP in a clean fashion so the vcd's are good."

**Implementation:**
```python
# bin/CocoTBFramework/components/gaxi/gaxi_master.py

# BEFORE:
self.log.error(f"Master({self.title}) Phase2: TIMEOUT ...")
return False  # Continue running despite timeout

# AFTER:
self.log.error(f"Master({self.title}) Phase2: TIMEOUT ...")
raise cocotb.result.TestFailure(
    f"Master({self.title}) TIMEOUT: No ready signal after {self.timeout_cycles} cycles. "
    "Check RTL for backpressure issues or increase timeout_cycles if legitimate delay."
)
```

**Benefits:**
- Test exits immediately on timeout (no wasted time)
- VCD files are properly closed and available for debugging
- Clear failure message points to issue
- cocotb.result.TestFailure is the standard way to fail tests cleanly

---

### 3. Parallel Execution Enabled ✅

**User Requirement:**
> "Please keep parallel execution going. That should be fine as long as all of the test names are unique."

**Implementation:**
```python
# dv/tests/conftest.py

# REMOVED parallel-disable code
# Parallel execution now works normally with pytest-xdist

# Just added comment:
# Parallel execution is OK - all test names are unique
# Memory limit of 32GB in TBs handles Verilator memory usage
```

**Test Name Uniqueness:**
All tests have unique names following pattern: `test_bridge_{config}_{test_type}`

```
test_bridge_1x2_rd_basic_connectivity  ✓ Unique
test_bridge_1x2_rd_address_decode      ✓ Unique
test_bridge_1x2_wr_basic_connectivity  ✓ Unique
test_bridge_1x2_wr_address_decode      ✓ Unique
...
test_bridge_5x3_channels_arbitration   ✓ Unique
```

**Parallel Execution Benefits:**
- Faster test completion (22 tests in parallel vs sequential)
- Better CPU utilization
- No name conflicts with unique test names

---

### 4. Memory Limit: 32GB ✅

**User Requirement:**
> "Memory should be like 32GB; that should be totally safe."

**Implementation:**
```python
# All bridge testbenches:
def __init__(self, dut):
    safety_limits = {
        'max_memory_mb': 32768,  # 32GB limit (safe for bridge tests)
        'enable_safety_monitoring': True,
    }
    super().__init__(dut, safety_limits=safety_limits)
```

**Rationale:**
- Verilator reports total system memory (20-80GB typical)
- 32GB limit allows normal operation while catching true leaks
- Safety monitoring still active, just with realistic threshold

---

### 5. APB Clock (pclk) - Not Needed ℹ️

**User Requirement:**
> "IF THE AXI CLOCK for the bridge is 10ns, keep the pclk for apb at 15ns."

**Analysis:**
Bridge testbenches test the bridge crossbar, which is a synchronous design running on aclk (10ns).

- **Bridge:** Synchronous crossbar, single clock domain (aclk = 10ns)
- **APB Peripheral:** External to bridge, would have its own pclk
- **Not Needed:** Bridge tests don't instantiate actual APB peripherals

**If APB peripherals were added:**
```python
# Hypothetical APB peripheral testbench:
await self.start_clock('aclk', freq=10, units='ns')   # AXI side
await self.start_clock('pclk', freq=15, units='ns')   # APB side (slower)
```

But for current bridge tests, only aclk exists.

---

## Impact Summary

| Item | Before | After | Status |
|------|--------|-------|--------|
| GAXI Timeout | 1000 cycles | 200 cycles | ✅ Fixed |
| Timeout Behavior | Log error, continue | Raise TestFailure | ✅ Fixed |
| Parallel Execution | Disabled | Enabled | ✅ Fixed |
| Memory Limit | 2048 MB | 32768 MB | ✅ Fixed |
| APB Clock | N/A | N/A (not needed) | ℹ️ Clarified |

---

## Test Execution

**Safe execution:**
```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/bridge/dv/tests

# Parallel execution (default with pytest-xdist)
pytest -v

# Or explicit parallel control
pytest -n auto -v

# Single test for debugging
pytest test_bridge_1x2_rd.py::test_bridge_1x2_rd_basic_connectivity -v
```

**Expected Behavior:**
- ✅ Tests run in parallel
- ✅ Memory usage stays under 32GB limit
- ✅ Timeouts fail quickly (200 cycles) with clean VCD
- ✅ No system crashes

---

## Files Modified

### Bridge Testbenches (12 files)
All with memory limit and timeout_cycles=200:

- `dv/tbclasses/bridge1x2_rd_tb.py`
- `dv/tbclasses/bridge1x2_wr_tb.py`
- `dv/tbclasses/bridge1x3_rd_tb.py`
- `dv/tbclasses/bridge1x3_wr_tb.py`
- `dv/tbclasses/bridge1x4_rd_tb.py`
- `dv/tbclasses/bridge1x4_wr_tb.py`
- `dv/tbclasses/bridge1x5_rd_tb.py`
- `dv/tbclasses/bridge1x5_wr_tb.py`
- `dv/tbclasses/bridge2x2_rw_tb.py`
- `dv/tbclasses/bridge5x3_channels_tb.py`
- `dv/tbclasses/bridge_apb_bridge_tb.py`
- `dv/tbclasses/bridge_test_apb_bridge_tb.py`

### Framework (1 file)
- `bin/CocoTBFramework/components/gaxi/gaxi_master.py` - Timeout raises TestFailure

### Configuration (1 file)
- `dv/tests/conftest.py` - Parallel execution enabled

### Documentation (3 files)
- `dv/tests/README_TEST_EXECUTION.md` - Updated with corrections
- `BUGFIX_2025-11-10_TEST_CRASHES.md` - Original fix documentation
- `CORRECTIONS_2025-11-10.md` - This file

---

## Changelog

**2025-11-10 (Corrections):**
- Changed GAXI timeout from 10000 → 200 cycles (per user requirement)
- Added TestFailure exception on timeout for clean VCD exit
- Re-enabled parallel execution (test names are unique)
- Kept 32GB memory limit (per user confirmation)
- Clarified APB clock not needed in bridge tests

**2025-11-10 (Initial):**
- Fixed memory safety limit from 2GB → 32GB
- Attempted timeout fix (corrected above)
- Disabled parallel execution (re-enabled above)

---

**Status:** ✅ CORRECTED - Ready for testing
**Corrections Applied:** 4 critical items
**Total Changes:** 85 instances across 14 files
