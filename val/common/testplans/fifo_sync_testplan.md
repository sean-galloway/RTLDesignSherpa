# Test Plan: fifo_sync

## Module: rtl/common/fifo_sync.sv
## Test File: val/common/test_fifo_buffer.py
## Current Coverage: ~85%

## Scenarios

| ID | Scenario | Description | Tested | Coverage Gap |
|----|----------|-------------|--------|--------------|
| FS-01 | Basic write/read | Single write followed by read | YES | - |
| FS-02 | Fill to full | Write until FIFO full | YES | - |
| FS-03 | Drain to empty | Read until FIFO empty | YES | - |
| FS-04 | Simultaneous R/W | Read and write same cycle | YES | - |
| FS-05 | Write when full | Attempt write to full FIFO | NO | Error path uncovered |
| FS-06 | Read when empty | Attempt read from empty FIFO | NO | Error path uncovered |
| FS-07 | Almost full flag | Verify almost_full threshold | YES | - |
| FS-08 | Almost empty flag | Verify almost_empty threshold | YES | - |
| FS-09 | REGISTERED=0 (mux) | Combinational read path | YES | - |
| FS-10 | REGISTERED=1 (flop) | Registered read path | YES | - |
| FS-11 | Various depths (4,8,16) | Different FIFO depths | YES | - |

## Uncovered Lines Analysis

```
%000005                 always_comb w_rd_data = mem[r_rd_addr];
%000000         if (write && wr_full) begin
%000000             $timeformat(-9, 3, " ns", 10);
%000000             $display("Error: %s write while fifo full, %t", INSTANCE_NAME, $time);
%000000         if (read && rd_empty) begin
%000000             $timeformat(-9, 3, " ns", 10);
%000000             if (REGISTERED == 1)
%000000                 $display("Error: %s read while fifo empty (flop mode), %t", INSTANCE_NAME, $time);
```

## Action Items

1. **FS-05**: Add test that intentionally writes to a full FIFO
   - This exercises the error detection path
   - Expect $display error message in simulation
   - Data should NOT be written (verify FIFO contents unchanged)

2. **FS-06**: Add test that intentionally reads from an empty FIFO
   - This exercises the error detection path
   - Expect $display error message in simulation
   - Read data should be undefined/stale

3. **Note**: These are error condition tests. The FIFO should survive these
   conditions (not corrupt) but they represent protocol violations.

## Recommended Test Additions

```python
async def test_write_when_full_error(dut):
    """Test error detection when writing to full FIFO"""
    # 1. Fill FIFO to capacity
    # 2. Attempt one more write
    # 3. Verify FIFO contents unchanged
    # 4. (Error message appears in log)

async def test_read_when_empty_error(dut):
    """Test error detection when reading from empty FIFO"""
    # 1. Ensure FIFO is empty
    # 2. Attempt a read
    # 3. Verify rd_valid stays low (or check behavior)
```

## Test Commands

```bash
# Run with coverage
COVERAGE=1 REG_LEVEL=FUNC pytest val/common/test_fifo_buffer.py -v
```
