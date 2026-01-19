# Test Plan: counter_johnson

## Module: rtl/common/counter_johnson.sv
## Test File: val/common/test_counter_johnson.py
## Current Coverage: ~85%

## Module Overview

Johnson counter (twisted ring counter) - shifts counter_gray with feedback from inverted MSB.
Creates a 2*WIDTH state sequence where only one bit changes per clock.

## Scenarios

| ID | Scenario | Description | Tested | Coverage Gap |
|----|----------|-------------|--------|--------------|
| CJ-01 | Reset state | counter_gray = 0 after reset | YES | - |
| CJ-02 | Enable counting | Increment when enable=1 | YES | - |
| CJ-03 | Disable hold | Hold value when enable=0 | PARTIAL | enable=0 path |
| CJ-04 | Full sequence | Complete 2*WIDTH state cycle | UNKNOWN | May need verification |
| CJ-05 | Reset during count | Reset in middle of sequence | PARTIAL | rst_n transitions |
| CJ-06 | Enable toggle | Rapid enable on/off | NO | enable toggling |
| CJ-07 | Parameter WIDTH=4 | Default configuration | YES | - |
| CJ-08 | Parameter WIDTH=8 | Larger configuration | UNKNOWN | May not be tested |

## Uncovered Lines Analysis

```
%000007     input  logic                rst_n,
%000007     input  logic                enable,
%000008     )   // End of always_ff
```

The low hit counts on rst_n (7) and enable (7) vs clk (125) indicate:
- Reset is asserted/deasserted minimally
- Enable is toggled minimally
- Most cycles run with enable=1 continuously

## Root Cause Analysis

The test likely:
1. Asserts reset once at start
2. Enables counting and runs for many cycles
3. Doesn't test enable=0 hold behavior extensively
4. Doesn't test reset in middle of counting

## Action Items

1. **CJ-03/06**: Add enable toggle tests:
   - Count a few cycles, disable, verify hold
   - Rapid enable toggling (on/off each cycle)
   - Enable after long disable period

2. **CJ-05**: Add mid-count reset test:
   - Count to partial sequence
   - Assert reset
   - Verify immediate return to 0
   - Deassert and verify counting resumes

3. **CJ-04**: Verify full sequence coverage:
   - For WIDTH=4, complete all 8 states
   - Verify sequence wraps correctly

## Recommended Test Additions

```python
async def test_enable_hold(dut):
    """Test counter holds value when enable=0"""
    # Enable and count for a few cycles
    dut.enable.value = 1
    for _ in range(3):
        await RisingEdge(dut.clk)

    # Capture current value
    held_value = dut.counter_gray.value

    # Disable and verify hold
    dut.enable.value = 0
    for _ in range(5):
        await RisingEdge(dut.clk)
        assert dut.counter_gray.value == held_value

async def test_reset_during_count(dut):
    """Test reset in middle of counting sequence"""
    dut.enable.value = 1
    for _ in range(3):
        await RisingEdge(dut.clk)

    # Reset mid-count
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    assert dut.counter_gray.value == 0

    # Resume counting
    dut.rst_n.value = 1
    await RisingEdge(dut.clk)
```

## Test Commands

```bash
# Run with coverage
COVERAGE=1 REG_LEVEL=FUNC pytest val/common/test_counter_johnson.py -v
```
