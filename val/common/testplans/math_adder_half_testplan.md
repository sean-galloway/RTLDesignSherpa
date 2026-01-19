# Test Plan: math_adder_half

## Module: rtl/common/math_adder_half.sv
## Test File: val/common/test_math_adder_half.py
## Current Coverage: ~50% (NEEDS WORK)

## Module Overview

Simple combinational half adder:
- Two single-bit inputs: i_a, i_b
- Two outputs: ow_sum (XOR), ow_carry (AND)
- Purely combinational, no clock/reset

## Truth Table

| i_a | i_b | ow_sum | ow_carry |
|-----|-----|--------|----------|
| 0   | 0   | 0      | 0        |
| 0   | 1   | 1      | 0        |
| 1   | 0   | 1      | 0        |
| 1   | 1   | 0      | 1        |

## Scenarios

| ID | Scenario | Description | Tested | Coverage Gap |
|----|----------|-------------|--------|--------------|
| MAH-01 | Case 0+0 | i_a=0, i_b=0 → sum=0, carry=0 | PARTIAL | Low hit count |
| MAH-02 | Case 0+1 | i_a=0, i_b=1 → sum=1, carry=0 | PARTIAL | Low hit count |
| MAH-03 | Case 1+0 | i_a=1, i_b=0 → sum=1, carry=0 | PARTIAL | Low hit count |
| MAH-04 | Case 1+1 | i_a=1, i_b=1 → sum=0, carry=1 | PARTIAL | Low hit count |
| MAH-05 | All cases | Complete truth table | NO | Need full coverage |

## Uncovered Lines Analysis

```
%000001     input  logic i_a,
%000003     input  logic i_b,
%000002     output logic ow_sum,
%000001     output logic ow_carry
```

Very low hit counts (1-3) indicate minimal exercise of this module. All four input combinations should be tested multiple times.

## Root Cause Analysis

This is a combinational module used as a building block in larger adders. The test may:
1. Only test one or two input combinations
2. Be instantiated inside another module that doesn't exercise all paths
3. Have a very short test duration

## Action Items

1. **MAH-01 to MAH-04**: Test all input combinations:
   - Exhaustively test all 4 cases
   - Verify both sum and carry for each

2. **MAH-05**: Run multiple iterations:
   - Test each case multiple times
   - Add random pattern testing

## Recommended Test Additions

```python
async def test_truth_table_exhaustive(dut):
    """Test all input combinations of half adder"""
    test_cases = [
        # (i_a, i_b, expected_sum, expected_carry)
        (0, 0, 0, 0),
        (0, 1, 1, 0),
        (1, 0, 1, 0),
        (1, 1, 0, 1),
    ]

    for i_a, i_b, exp_sum, exp_carry in test_cases:
        dut.i_a.value = i_a
        dut.i_b.value = i_b
        await Timer(1, units='ns')  # Combinational settling

        assert dut.ow_sum.value == exp_sum, f"Sum failed for {i_a}+{i_b}"
        assert dut.ow_carry.value == exp_carry, f"Carry failed for {i_a}+{i_b}"

async def test_random_patterns(dut):
    """Test with random patterns for stress coverage"""
    import random
    for _ in range(100):
        i_a = random.randint(0, 1)
        i_b = random.randint(0, 1)

        dut.i_a.value = i_a
        dut.i_b.value = i_b
        await Timer(1, units='ns')

        assert dut.ow_sum.value == (i_a ^ i_b)
        assert dut.ow_carry.value == (i_a & i_b)
```

## Test Commands

```bash
# Run with coverage
COVERAGE=1 REG_LEVEL=FUNC pytest val/common/test_math_adder_half.py -v
```

## Priority

**MEDIUM** - Basic building block, but low coverage indicates test gaps.
