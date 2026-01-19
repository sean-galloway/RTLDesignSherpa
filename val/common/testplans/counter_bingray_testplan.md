# Test Plan: counter_bingray

## Module: rtl/common/counter_bingray.sv
## Test File: val/common/test_counter_bingray.py
## Current Coverage: ~85%

## Module Overview

Binary counter with simultaneous Gray code output for async FIFO pointer management:
- Binary output (counter_bin) for memory addressing
- Gray code output (counter_gray) for CDC synchronization
- Next value prediction (counter_bin_next) for look-ahead logic

## Scenarios

| ID | Scenario | Description | Tested | Coverage Gap |
|----|----------|-------------|--------|--------------|
| CBG-01 | Reset state | All outputs = 0 after reset | YES | - |
| CBG-02 | Enable counting | Increment when enable=1 | YES | - |
| CBG-03 | Disable hold | Hold value when enable=0 | PARTIAL | enable=0 path |
| CBG-04 | Binary output | counter_bin increments correctly | YES | - |
| CBG-05 | Gray output | counter_gray follows Gray code | YES | - |
| CBG-06 | Bin-Gray sync | Binary and Gray synchronized | YES | - |
| CBG-07 | Next value | counter_bin_next = bin + 1 | PARTIAL | Output exercised |
| CBG-08 | Wraparound | 2^WIDTH wrap | YES | - |
| CBG-09 | Single-bit change | Gray changes only 1 bit/cycle | UNKNOWN | Need verification |
| CBG-10 | Parameter WIDTH=4 | Default configuration | YES | - |
| CBG-11 | Parameter WIDTH=8 | Larger configuration | UNKNOWN | May not be tested |

## Uncovered Lines Analysis

```
%000000     output logic [WIDTH-1:0] counter_bin,
%000000     output logic [WIDTH-1:0] counter_bin_next,
%000000     output logic [WIDTH-1:0] counter_gray
%000000     logic [WIDTH-1:0] w_counter_bin, w_counter_gray;
```

The 0 hits on output ports and internal wires are typical of Verilator coverage for multi-bit signals. The actual logic is well-exercised:
- Clock: 1150 hits
- rst_n/enable: 42 hits
- always_ff: 596 hits

## Root Cause Analysis

The apparent low coverage on outputs is due to Verilator's treatment of vector signals. The functional paths are covered based on the always_ff hit counts.

**True gaps:**
- enable=0 hold behavior needs more testing
- Various WIDTH configurations

## Action Items

1. **CBG-03**: Test enable=0 hold:
   - Count for several cycles
   - Disable enable, verify all outputs hold
   - Re-enable and verify counting resumes

2. **CBG-09**: Verify Gray code property:
   - Check that counter_gray changes exactly 1 bit per increment
   - Test across wraparound boundary

3. **CBG-11**: Test larger WIDTH:
   - WIDTH=8 or WIDTH=16 configuration
   - Verify Gray code property still holds

## Recommended Test Additions

```python
async def test_enable_hold(dut):
    """Test counter holds when enable=0"""
    dut.enable.value = 1
    for _ in range(5):
        await RisingEdge(dut.clk)

    # Capture current values
    held_bin = dut.counter_bin.value
    held_gray = dut.counter_gray.value

    # Disable and verify hold
    dut.enable.value = 0
    for _ in range(10):
        await RisingEdge(dut.clk)
        assert dut.counter_bin.value == held_bin
        assert dut.counter_gray.value == held_gray

async def test_gray_single_bit_change(dut):
    """Verify Gray code changes exactly 1 bit per increment"""
    dut.enable.value = 1
    prev_gray = dut.counter_gray.value

    for _ in range(2**WIDTH - 1):  # Full cycle
        await RisingEdge(dut.clk)
        curr_gray = dut.counter_gray.value
        # XOR to find changed bits, popcount should be 1
        diff = prev_gray ^ curr_gray
        assert bin(diff).count('1') == 1
        prev_gray = curr_gray
```

## Test Commands

```bash
# Run with coverage
COVERAGE=1 REG_LEVEL=FUNC pytest val/common/test_counter_bingray.py -v
```
