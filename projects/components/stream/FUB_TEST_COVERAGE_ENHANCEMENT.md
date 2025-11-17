# FUB Test Coverage Enhancement

**Date:** 2025-11-12
**Purpose:** Address critical gaps in FUB-level testing that allowed bugs to escape to macro testing
**Severity:** HIGH - Completion signal bug escaped because AXI engines had NO FUB tests

---

## Executive Summary

**CRITICAL FINDING**: The AXI read and write engines had **ZERO** FUB-level tests, allowing a critical completion signal bug to escape to macro testing where it caused all 25 tests to hang.

**Root Cause**: `axi_rd_all_complete` and `axi_wr_all_complete` were combinational signals that pulsed HIGH/LOW as `outstanding_count` changed, instead of being sticky registers.

**Impact**:
- All 25 macro-level tests hung waiting for completion signals
- Bug not caught until extensive debugging of core tests
- Wasted ~2 hours of debugging time
- User lost confidence in test coverage

**Solution**: Create comprehensive FUB tests for all datapath modules with focus on:
1. Completion signal stability
2. Multi-burst operation
3. Outstanding transaction tracking
4. Edge cases that stress control logic

---

## Gap Analysis

### Modules WITH FUB Tests

| Module | Test File | Coverage Assessment |
|--------|-----------|---------------------|
| `descriptor_engine.sv` | `test_descriptor_engine.py` | ✅ Good - descriptor fetch validated |
| `scheduler.sv` | `test_scheduler.py` | ✅ Good - recently enhanced with concurrent R/W test |
| `sram_controller.sv` | `test_sram_controller.py` | ⚠️ Basic - needs stress testing |
| `perf_profiler.sv` | `test_perf_profiler.py` | ✅ Good - event monitoring validated |
| `apbtodescr.sv` | `test_apbtodescr.py` | ✅ Good - APB interface validated |

### Modules WITHOUT FUB Tests (CRITICAL GAP!)

| Module | Status | Impact | Priority |
|--------|--------|--------|----------|
| `axi_read_engine.sv` | ❌ NO TESTS | **HIGH** - Completion signal bug escaped | P0 |
| `axi_write_engine.sv` | ❌ NO TESTS | **HIGH** - Completion signal bug escaped | P0 |
| `simple_sram.sv` | ❌ NO TESTS | **MEDIUM** - Simple memory, low risk | P1 |

---

## New Test Coverage

### 1. AXI Read Engine (`test_axi_read_engine.py`) ✅ CREATED

**Purpose**: Validate AXI read engine operation and catch completion signal bugs

**Test Cases**:

#### `test_single_burst_completion`
- **What**: Issue single AR request, receive R responses, validate completion signal
- **Why**: Catches basic completion logic bugs
- **Level**: gate (1 burst), func (2 bursts), full (4 bursts)

#### `test_multi_burst_completion` ⭐ **CRITICAL**
- **What**: Issue multiple back-to-back AR requests, validate completion signal STAYS HIGH
- **Why**: **This would have caught the pulsing bug!**
  - Completion signal goes HIGH/LOW as outstanding_count changes
  - Multi-burst operation exposes false pulses between bursts
  - Validates sticky behavior
- **Level**: gate (2 bursts), func (4 bursts), full (8 bursts)

#### `test_outstanding_tracking`
- **What**: Issue AR, monitor outstanding_count, receive R, verify count==0
- **Why**: Validates fundamental counter logic
- **Level**: All levels

#### `test_channel_arbitration`
- **What**: Multiple channels requesting simultaneously, validate round-robin
- **Why**: Ensures fair arbitration, no starvation
- **Level**: func (2-4 channels), full (8 channels)

#### `test_sram_space_awareness`
- **What**: Limit SRAM space, verify engine doesn't issue AR when space insufficient
- **Why**: Prevents SRAM overflow, validates backpressure
- **Level**: func/full only

#### `test_pipelined_mode`
- **What**: PIPELINE=1, multiple outstanding AR per channel
- **Why**: Validates advanced pipelining mode
- **Level**: full only

**Assertions**:
```python
# CRITICAL: Completion signal must be sticky!
def validate_completion_sticky(changes):
    went_high = False
    for change in changes:
        if change['value'] == 1:
            went_high = True
        elif went_high and change['value'] == 0:
            # BUG! Went LOW after going HIGH
            return False
    return True
```

**Test Levels**:
- **gate**: 1 channel, 2 bursts, ~30s
- **func**: 2-4 channels, 4 bursts, ~90s
- **full**: 8 channels, 8 bursts, pipelined, ~180s

---

### 2. AXI Write Engine (`test_axi_write_engine.py`) - TO BE CREATED

**Purpose**: Validate AXI write engine operation (mirror of read engine tests)

**Test Cases** (same structure as read engine):
- `test_single_burst_completion`
- `test_multi_burst_completion` ⭐ **CRITICAL**
- `test_outstanding_tracking` (AW + W + B)
- `test_channel_arbitration`
- `test_sram_drain_awareness`
- `test_pipelined_mode`

**Key Differences from Read**:
- Track AW + W + B phases (3 channels vs AR + R 2 channels)
- Outstanding count: `AW_count - B_count`
- Drain data from SRAM instead of fill

---

### 3. SRAM Controller Enhancement

**Current**: `test_sram_controller.py` exists but basic

**Enhancements Needed**:
- Stress test: Rapid fill/drain cycles
- Backpressure validation: full → write blocked, empty → read blocked
- Multi-channel concurrent access
- Space allocation pre-allocation handshake

---

## Test Strategy Summary

### Testing Pyramid (Bottom-Up)

```
                    Macro Tests (stream_core)
                    ▲
                    │ Integration validation
                    │ Full datapath + control
        ┌───────────┴───────────┐
        │   FUB Tests            │
        │   ▲                    │
        │   │ Component validation
        │   │ Catch bugs EARLY   │
    ┌───┴───┴───┐                │
    │ Unit Tests │                │
    │ (if needed)│                │
    └───────────┘                │
                                  │
```

**RULE**: Bugs should be caught at the LOWEST possible level!

- **Unit**: Individual functions (rare in RTL)
- **FUB**: Individual modules (axi_read_engine, scheduler, etc.)
  - ✅ Catch completion signal bugs HERE
  - ✅ Catch arbitration bugs HERE
  - ✅ Catch outstanding tracking bugs HERE
- **Macro**: Integration (stream_core)
  - ✅ Catch interface mismatch bugs
  - ✅ Catch end-to-end flow bugs
  - ❌ Should NOT catch FUB-level bugs!

---

## Implementation Plan

### Phase 1: Critical Path (P0) - DONE/IN PROGRESS

| Task | Status | File | Notes |
|------|--------|------|-------|
| Create axi_read_engine test | ✅ DONE | `test_axi_read_engine.py` | Comprehensive coverage |
| Create axi_write_engine test | 🔄 IN PROGRESS | `test_axi_write_engine.py` | Mirror of read test |
| Run gate-level FUB tests | ⏳ PENDING | All FUB tests | Validate tests pass |

### Phase 2: Enhancement (P1)

| Task | Status | Notes |
|------|--------|-------|
| Enhance sram_controller test | ⏳ PENDING | Add stress testing |
| Add simple_sram test | ⏳ PENDING | Basic memory validation |
| Create FUB test Makefile targets | ⏳ PENDING | run-fub-datapaths-{gate/func/full} |

### Phase 3: Documentation (P2)

| Task | Status | Notes |
|------|--------|-------|
| Document FUB test requirements | ⏳ PENDING | Add to PRD.md |
| Create FUB test template | ⏳ PENDING | Standardize test structure |
| Update CLAUDE.md with testing guidance | ⏳ PENDING | Emphasize FUB-first |

---

## Lessons Learned

### What Went Wrong

1. **Gap**: AXI engines had zero FUB tests
2. **Assumption**: Macro tests would catch all bugs
3. **Reality**: Macro tests caught bug, but debugging was painful and time-consuming

### What We're Fixing

1. **Coverage**: Every FUB module MUST have comprehensive tests
2. **Focus**: Tests MUST validate edge cases, not just happy paths
3. **Assertions**: Tests MUST check control signals (completion, outstanding counts, etc.)
4. **Levels**: gate (quick smoke), func (typical use), full (stress + edge cases)

### Rules Going Forward

1. ✅ **NO new FUB module without FUB test**
2. ✅ **FUB tests MUST test edge cases** (multi-burst, backpressure, arbitration)
3. ✅ **FUB tests MUST validate control signals** (completion, outstanding, ready/valid)
4. ✅ **Run FUB tests BEFORE macro tests** (catch bugs early)
5. ✅ **Bugs found in macro tests trigger FUB test enhancement** (prevent regression)

---

## Testing Philosophy

### The Completion Signal Bug Case Study

**Bug**: `axi_rd_all_complete` was combinational, pulsed HIGH/LOW as `outstanding_count` changed

**Why Macro Test Caught It**:
- Macro test waited for `scheduler_idle && rd_complete && wr_complete`
- Signals never all HIGH simultaneously
- Test hung at 100% CPU

**Why FUB Test Should Have Caught It**:
```python
# FUB test would have monitored completion signal over time
completion_changes = []
for cycle in range(1000):
    if complete != prev_complete:
        completion_changes.append((cycle, complete))

# Assertion: Once HIGH, must stay HIGH
went_high = False
for cycle, value in completion_changes:
    if value == 1:
        went_high = True
    elif went_high and value == 0:
        # BUG! Signal went LOW after going HIGH
        assert False, "Completion signal pulsed!"
```

**Impact of FUB Test**:
- ✅ Bug caught in ~30 second FUB test
- ✅ Clear failure message: "Completion signal pulsed!"
- ✅ VCD shows exact cycle where bug occurs
- ✅ No need to debug complex macro test
- ✅ Fast fix iteration (FUB tests run quickly)

---

## Metrics

### Before Enhancement

| Metric | Value | Status |
|--------|-------|--------|
| FUB modules | 8 | - |
| FUB modules with tests | 5 | 62.5% |
| **Datapath modules with tests** | **0/2** | **0%** ❌ |
| Bugs escaped to macro | 1 (completion signal) | ❌ |

### After Enhancement (Target)

| Metric | Value | Status |
|--------|-------|--------|
| FUB modules | 8 | - |
| FUB modules with tests | 8 | 100% ✅ |
| **Datapath modules with tests** | **2/2** | **100%** ✅ |
| Bugs escaped to macro | 0 (goal) | ✅ |

---

## Conclusion

The completion signal bug exposed a critical gap in FUB-level testing. By creating comprehensive tests for the AXI read and write engines, we:

1. ✅ Catch bugs at the appropriate level (FUB, not macro)
2. ✅ Reduce debugging time (30s FUB test vs 1hr macro debugging)
3. ✅ Increase confidence in code quality
4. ✅ Prevent regression with targeted assertions
5. ✅ Establish testing standards for future FUB modules

**Key Takeaway**: **Every FUB module MUST have comprehensive tests that validate not just happy paths, but edge cases and control signal behavior.**

---

**Documentation and implementation support by Claude.**
