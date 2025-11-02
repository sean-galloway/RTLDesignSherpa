# Descriptor Engine Waveform Analysis Guide

## VCD File Location
```
val/rapids/fub_tests/descriptor_engine/local_sim_build/test_descriptor_engine_basic_nc32_aw64_dw0512_iw08_master/dump.vcd
```

**Size:** 335KB
**Test:** Basic level (passes - this is the working case)

## How to View

### Option 1: GTKWave (GUI)
```bash
cd /mnt/data/github/rtldesignsherpa
gtkwave val/rapids/fub_tests/descriptor_engine/local_sim_build/test_descriptor_engine_basic_nc32_aw64_dw0512_iw08_master/dump.vcd
```

### Option 2: Copy to your local machine
```bash
# On your local machine:
scp user@host:/mnt/data/github/rtldesignsherpa/val/rapids/fub_tests/descriptor_engine/local_sim_build/test_descriptor_engine_basic_nc32_aw64_dw0512_iw08_master/dump.vcd .
gtkwave dump.vcd
```

## Critical Signals to Examine

### FSM State and Control
```
descriptor_engine
  ├─ clk
  ├─ rst_n
  ├─ r_current_state          ← FSM state (IDLE=0, ISSUE_ADDR=1, WAIT_DATA=2, COMPLETE=3, ERROR=4)
  ├─ w_next_state
  ├─ r_apb_operation_active   ← **KEY: APB operation flag**
  └─ r_rda_operation_active   ← **KEY: RDA operation flag**
```

### APB Interface
```
descriptor_engine
  ├─ apb_valid
  ├─ apb_ready
  ├─ apb_addr
  ├─ w_apb_skid_valid_out     ← APB data available in skid buffer
  └─ w_apb_skid_ready_out     ← RTL ready to accept APB (line 242 logic)
```

### RDA Interface
```
descriptor_engine
  ├─ rda_valid
  ├─ rda_ready
  ├─ rda_packet
  ├─ rda_channel
  ├─ w_rda_skid_valid_out     ← RDA data available in skid buffer
  └─ w_rda_skid_ready_out     ← RTL ready to accept RDA (line 270 logic)
```

### Descriptor Output
```
descriptor_engine
  ├─ descriptor_valid         ← Descriptor output pulse
  ├─ descriptor_ready
  ├─ descriptor_packet
  ├─ descriptor_is_rda        ← Indicates RDA vs APB descriptor
  └─ descriptor_same
```

### AXI4 Read Interface
```
descriptor_engine
  ├─ ar_valid
  ├─ ar_ready
  ├─ ar_addr
  ├─ r_valid
  ├─ r_ready
  ├─ r_data
  ├─ r_axi_read_active        ← AXI transaction in progress
  └─ r_axi_read_addr
```

### Descriptor FIFO
```
descriptor_engine
  ├─ w_desc_fifo_wr_valid     ← Writing to descriptor FIFO
  ├─ w_desc_fifo_wr_ready     ← FIFO has space
  ├─ w_desc_fifo_rd_valid     ← Descriptor available at FIFO output
  └─ w_desc_fifo_rd_ready
```

## What to Look For

### Scenario: Sequential APB→RDA Pattern Failure

**Expected Timeline:**
1. **APB Operation (works):**
   - apb_valid=1, apb_ready=1 handshake
   - r_apb_operation_active rises to 1
   - FSM: IDLE → ISSUE_ADDR → WAIT_DATA → COMPLETE → IDLE
   - r_apb_operation_active should fall to 0 when FSM reaches COMPLETE and w_desc_fifo_wr_ready=1
   - descriptor_valid=1 pulse (APB descriptor output)

2. **Wait Period (~50 cycles):**
   - FSM should be in IDLE state
   - r_apb_operation_active should be 0
   - r_rda_operation_active should be 0

3. **RDA Operation (fails in concurrent test):**
   - rda_valid=1, check if rda_ready=1
   - **CRITICAL:** Check w_rda_skid_ready_out signal
   - If w_rda_skid_ready_out=0, this confirms RDA is being blocked
   - Check r_apb_operation_active value at this time
   - **Expected:** Should be 0 (APB completed long ago)
   - **If 1:** This confirms the bug - APB flag not clearing properly

### Key Investigation Points

1. **When does r_apb_operation_active clear?**
   - Find the COMPLETE state cycle
   - Verify w_desc_fifo_wr_ready=1 at that time
   - Check if r_apb_operation_active falls on next cycle

2. **Why does w_rda_skid_ready_out remain 0?**
   - Line 270 logic: `w_rda_skid_ready_out = (r_current_state == read_IDLE) && !r_apb_operation_active && !r_channel_reset_active`
   - Check all three conditions when RDA arrives

3. **Is there a descriptor FIFO backpressure issue?**
   - Check w_desc_fifo_wr_ready throughout APB operation
   - If it ever goes to 0, APB flag won't clear (line 452-453 condition)

## GTKWave Tips

### Adding Signals
1. Expand "descriptor_engine" in hierarchy browser
2. Select signals from list above
3. Right-click → "Insert" or drag to waveform window

### Viewing FSM States
1. Select r_current_state
2. Right-click → Data Format → Enum
3. Or add to "Translate Filter" with state names:
   - 0 = IDLE
   - 1 = ISSUE_ADDR
   - 2 = WAIT_DATA
   - 3 = COMPLETE
   - 4 = ERROR

### Finding Key Events
1. Search for rising edge of apb_valid (APB start)
2. Search for rising edge of descriptor_valid (descriptor output)
3. Search for rising edge of rda_valid (RDA start)
4. Measure time between events

### Zoom and Navigate
- Zoom to fit: View → Zoom → Zoom Fit
- Zoom to range: Select time range, Ctrl+Shift+Z
- Find next edge: Right-click signal → Search → Next Edge

## Expected Findings

**This VCD is from a PASSING test**, so it will show CORRECT behavior:
- Both APB and RDA operations should complete successfully
- r_apb_operation_active should clear properly
- w_rda_skid_ready_out should be 1 when RDA arrives

**To see the FAILURE**, we need a VCD from the concurrent test that times out.

## Generating Failure Case VCD

To capture waveform from the failing concurrent test:

```bash
cd /mnt/data/github/rtldesignsherpa

# Run single basic test with waveform capture enabled
pytest "val/rapids/fub_tests/descriptor_engine/test_descriptor_engine.py::test_descriptor_engine[basic-32-64-512-8]" -v --waves

# The VCD will be in:
# val/rapids/fub_tests/descriptor_engine/local_sim_build/test_descriptor_engine_basic_nc32_aw64_dw0512_iw08_<worker>/dump.vcd
```

Note: The basic test should show the failure in the concurrent test method within that test run.

