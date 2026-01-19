# Test Plans Index - val/common

## Overview

This directory contains test plans for modules in `rtl/common/` that have coverage gaps.
Each test plan documents:
- Current coverage status
- Test scenarios and their coverage status
- Uncovered lines analysis
- Root cause analysis
- Recommended test additions

## Coverage Summary

| Module | Current Coverage | Priority | Key Gaps |
|--------|-----------------|----------|----------|
| [counter_load_clear](counter_load_clear_testplan.md) | ~70% | **HIGH** | loadval NOT tested (0 hits!) |
| [arbiter_priority_encoder](arbiter_priority_encoder_testplan.md) | ~60% | **HIGH** | requests_masked, casez cases |
| [math_adder_half](math_adder_half_testplan.md) | ~50% | MEDIUM | Minimal input combinations |
| [counter_johnson](counter_johnson_testplan.md) | ~85% | LOW | enable toggle, reset mid-count |
| [counter_ring](counter_ring_testplan.md) | ~85% | LOW | enable toggle, reset mid-rotation |
| [counter_bingray](counter_bingray_testplan.md) | ~85% | LOW | enable=0 hold path |
| [counter_bin](counter_bin_testplan.md) | ~90% | LOW | Optional outputs |
| [fifo_sync](fifo_sync_testplan.md) | ~85% | LOW | Error conditions (full/empty) |
| [arbiter_round_robin](arbiter_round_robin_testplan.md) | ~85% | LOW | grant_ack handshake |
| [arbiter_round_robin_simple](arbiter_round_robin_simple_testplan.md) | ~90% | LOW | Reset exercises |

## Priority Ranking

### HIGH Priority (Critical gaps in main functionality)

1. **counter_load_clear** - Load functionality completely untested!
   - loadval input: 0 hits
   - r_match_val register: 0 hits
   - The main feature (programmable match) is NOT tested

2. **arbiter_priority_encoder** - Masked request path untested
   - requests_masked: 0 hits
   - casez priority cases incomplete
   - any_masked_requests: not exercised

### MEDIUM Priority (Basic functionality gaps)

3. **math_adder_half** - Very low hit counts
   - All inputs: 1-3 hits only
   - Need exhaustive truth table testing

### LOW Priority (Minor gaps in secondary paths)

4-10. Counter and arbiter modules have good overall coverage but could improve:
   - Enable/disable toggle testing
   - Reset mid-operation testing
   - Parameter variation testing

## Running Tests with Coverage

```bash
# Run all common tests with coverage
cd /mnt/data/github/rtldesignsherpa
COVERAGE=1 REG_LEVEL=FUNC pytest val/common/ -v --tb=short

# Run specific module test with coverage
COVERAGE=1 pytest val/common/test_counter_load_clear.py -v

# View coverage annotation for specific module
verilator_coverage --annotate /tmp/my_cov val/common/coverage_data/merged/*.dat
```

## Coverage Target

**Goal: 95% combined coverage across val/common and val/amba**

Current status:
- val/common: ~76%
- val/amba: ~72%
- Combined: ~75%

Gap to 95%: ~20 percentage points

## Key Action Items

1. Fix HIGH priority test gaps first
2. Add comprehensive tests for counter_load_clear load functionality
3. Add masked request tests for arbiter_priority_encoder
4. Run comprehensive test suite after each fix
5. Re-analyze coverage to identify remaining gaps
