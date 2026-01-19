# Test Plan: counter_bin

## Module: rtl/common/counter_bin.sv
## Test File: val/common/test_counter_bin.py
## Current Coverage: ~95%

## Scenarios

| ID | Scenario | Description | Tested | Coverage Gap |
|----|----------|-------------|--------|--------------|
| CB-01 | Basic counting | Count from 0 to MAX_VALUE | YES | - |
| CB-02 | Overflow wrap | Verify counter wraps at MAX_VALUE | YES | - |
| CB-03 | Enable gating | Counter holds when enable=0 | YES | - |
| CB-04 | Reset behavior | Counter resets to 0 on rst_n=0 | YES | - |
| CB-05 | counter_bin_curr output | Verify current count output | NO | Line: output counter_bin_curr |
| CB-06 | counter_bin_next output | Verify next count output | NO | Line: output counter_bin_next |
| CB-07 | Various WIDTH values | Test WIDTH=4,8,16,32 | YES | - |
| CB-08 | Various MAX_VALUE | Test MAX_VALUE < 2^WIDTH | YES | - |

## Uncovered Lines Analysis

```
%000000     output logic [WIDTH-1:0] counter_bin_curr,
%000000     output logic [WIDTH-1:0] counter_bin_next
%000001     logic [WIDTH-2:0] w_max_val;
```

## Action Items

1. **CB-05/CB-06**: The `counter_bin_curr` and `counter_bin_next` outputs are optional debug ports.
   Tests should explicitly check these values if they exist on the DUT.

2. **CB-07**: The `w_max_val` internal signal may not be exercised in all configurations.
   Need to test with MAX_VALUE that exercises boundary conditions.

## Test Commands

```bash
# Run with coverage
COVERAGE=1 REG_LEVEL=FUNC pytest val/common/test_counter_bin.py -v

# Run specific parameterization
COVERAGE=1 pytest "val/common/test_counter_bin.py::test_counter_bin[8-128-medium]" -v
```
