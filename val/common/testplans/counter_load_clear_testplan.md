# Test Plan: counter_load_clear

## Module: rtl/common/counter_load_clear.sv
## Test File: val/common/test_counter_load_clear.py
## Current Coverage: **100.0** (Verilator line, measured 2026-08-07)

## Module Overview

Parameterizable up counter with load and clear functionality:
- Counts from 0 to programmable match value (r_match_val)
- Load operation captures loadval into match register
- Clear resets count to 0 (highest priority)
- Done flag when count == r_match_val

## Scenarios

| ID | Scenario | Description | Tested | Coverage Gap |
|----|----------|-------------|--------|--------------|
| CLC-01 | Reset state | count=0, r_match_val=0, done=1 | YES | - |
| CLC-02 | Load match value | loadval captured to r_match_val | YES | - |
| CLC-03 | Basic counting | Increment from 0 to match | YES | - |
| CLC-04 | Wraparound | count wraps to 0 after match | YES | - |
| CLC-05 | Clear priority | clear overrides increment | YES | - |
| CLC-06 | Done flag | done asserts at match | YES | - |
| CLC-07 | Load during count | Load new match while counting | YES | - |
| CLC-08 | Clear during count | Clear in middle of sequence | YES | - |
| CLC-09 | Hold state | increment=0 holds count | YES | - |
| CLC-10 | Immediate match | Load value equal to current count | YES | - |

## Coverage Status

**VERIFIED: 100% line/branch coverage achieved (2026-01-17)**

All test scenarios fully covered by `test_counter_load_clear.py`:
- `test_basic_counting()` - Covers CLC-01, CLC-03, CLC-06
- `test_clear_functionality()` - Covers CLC-05, CLC-08
- `test_load_functionality()` - Covers CLC-02, CLC-07
- `test_increment_control()` - Covers CLC-09
- `test_edge_cases()` - Covers CLC-04, CLC-10

The testbench uses `load_match_value()` helper method to exercise the loadval input path.

## Test Configurations

REG_LEVEL Control:
- GATE: 1 test (max=32, basic level)
- FUNC: 3 tests (all max_values, basic level)
- FULL: 9 tests (all max_values, all test levels)

## Test Commands

```bash
# Run with coverage
COVERAGE=1 REG_LEVEL=FUNC pytest val/common/test_counter_load_clear.py -v
```

## Priority

**NONE** - All coverage goals achieved.

<!-- ============================================================ -->

## External test audit (Kimi rounds 3-4, 2026-08-06/07)

The area's first external review of its test collateral, plus a scoped
re-round over what the fixes touched. 42 findings across both rounds; every
one triaged, none dropped on a verdict alone. All items below are FIXED unless
marked otherwise.

**What the rounds say about this plan's own claims.** A test plan records what
is *intended* to be covered. The audit measured what is actually *checked*, and
the gap was the story: mechanisms that existed but drove nothing, and
assertions that could not fail. A "Tested: YES" row is only as good as the
assertion behind it.

### counter_load_clear_wavedrom

- `r3` Wavedrom wrapper never plumbs TEST_LEVEL -- default runs emit only 2 of the 4 documented scenarios
- `r3` counter_load_clear_wavedrom hand-lists its sources instead of using a filelist
