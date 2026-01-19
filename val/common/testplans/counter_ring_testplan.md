# Test Plan: counter_ring

## Module: rtl/common/counter_ring.sv
## Test File: val/common/test_counter_ring.py
## Current Coverage: ~85%

## Module Overview

Ring counter (one-hot shift register):
- Initializes to 'b1 (LSB set)
- Right rotates when enabled: {ring_out[0], ring_out[WIDTH-1:1]}
- WIDTH states before returning to initial state

## Scenarios

| ID | Scenario | Description | Tested | Coverage Gap |
|----|----------|-------------|--------|--------------|
| CR-01 | Reset state | ring_out = 'b1 (LSB set) | YES | - |
| CR-02 | Enable rotation | Right rotate when enable=1 | YES | - |
| CR-03 | Disable hold | Hold value when enable=0 | PARTIAL | enable=0 path |
| CR-04 | Full cycle | Complete WIDTH rotations | UNKNOWN | May need verification |
| CR-05 | Reset during rotation | Reset in middle of sequence | PARTIAL | rst_n transitions |
| CR-06 | Enable toggle | Rapid enable on/off | NO | enable toggling |
| CR-07 | Parameter WIDTH=4 | Default configuration | YES | - |
| CR-08 | Parameter WIDTH=8 | Larger configuration | UNKNOWN | May not be tested |

## Uncovered Lines Analysis

```
%000009     input  wire             rst_n,    // Active low reset
%000005     input  wire             enable,   // Counter enable
%000008     )   // End of always_ff
```

The low hit counts indicate:
- rst_n (9 hits) - minimal reset assertions
- enable (5 hits) - minimal enable toggling
- Most test cycles run with enable=1 continuously

## Root Cause Analysis

Similar to counter_johnson:
1. Reset asserted once at start
2. Enable held high for counting
3. No testing of enable=0 hold behavior
4. No testing of reset during rotation

## Action Items

1. **CR-03/06**: Add enable toggle tests:
   - Rotate a few positions, disable, verify hold
   - Rapid enable toggling
   - Resume rotation after pause

2. **CR-05**: Add mid-rotation reset test:
   - Rotate to middle position
   - Assert reset
   - Verify return to 'b1
   - Resume rotation

3. **CR-04**: Verify full cycle:
   - For WIDTH=4, verify sequence: 0001→1000→0100→0010→0001
   - Confirm proper wraparound

## Recommended Test Additions

```python
async def test_enable_hold(dut):
    """Test counter holds position when enable=0"""
    # Rotate a few positions
    dut.enable.value = 1
    for _ in range(2):
        await RisingEdge(dut.clk)

    # Capture current position
    held_value = dut.ring_out.value

    # Disable and verify hold
    dut.enable.value = 0
    for _ in range(5):
        await RisingEdge(dut.clk)
        assert dut.ring_out.value == held_value

async def test_full_rotation_sequence(dut):
    """Test complete rotation sequence for WIDTH=4"""
    # Expected sequence for WIDTH=4 right rotate
    expected_sequence = [0b0001, 0b1000, 0b0100, 0b0010, 0b0001]

    dut.enable.value = 1
    for expected in expected_sequence:
        assert dut.ring_out.value == expected
        await RisingEdge(dut.clk)

async def test_reset_during_rotation(dut):
    """Test reset returns to initial state"""
    dut.enable.value = 1
    for _ in range(2):
        await RisingEdge(dut.clk)

    # Reset mid-rotation
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    assert dut.ring_out.value == 1  # Back to initial

    dut.rst_n.value = 1
    await RisingEdge(dut.clk)
```

## Test Commands

```bash
# Run with coverage
COVERAGE=1 REG_LEVEL=FUNC pytest val/common/test_counter_ring.py -v
```
