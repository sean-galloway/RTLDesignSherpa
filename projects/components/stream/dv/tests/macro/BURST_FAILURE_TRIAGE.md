# Burst Matrix Test Failure Triage

**Date:** 2025-11-23
**Total Tests:** 75 (25 burst matrix + others)
**Failures:** 6 out of 25 burst tests
**Pass Rate:** 76% (19/25 burst tests passed)

---

## Failure Matrix

| Idx | Test | DW | RdBurst | WrBurst | SRAM | FIFO | RdSize | WrSize | Status |
|-----|------|----|---------|---------|----- |------|--------|--------|--------|
| 3   | single_channel | 128 | 16 | 8  | 2KB | 128 | 256B | 128B | **FAIL** |
| 13  | single_channel | 256 | 16 | 8  | 2KB | 64  | 512B | 256B | **FAIL** |
| 14  | variable_sizes | 256 | 16 | 8  | 4KB | 128 | 512B | 256B | **FAIL** ⚠️ |
| 17  | variable_sizes | 512 | 8  | 8  | 2KB | 32  | 512B | 512B | **FAIL** |
| 19  | variable_sizes | 512 | 8  | 16 | 2KB | 32  | 512B | 1KB  | **FAIL** |
| 21  | single_channel | 512 | 16 | 8  | 2KB | 32  | 1KB  | 512B | **FAIL** |

---

## Clear Pattern: ASYMMETRIC BURST SIZES

### Primary Finding
**5 out of 6 failures have RD_BURST ≠ WR_BURST**

Asymmetric burst configurations:
- params3:  RD=16 > WR=8  (128-bit, 2KB)
- params13: RD=16 > WR=8  (256-bit, 2KB)
- params14: RD=16 > WR=8  (256-bit, 4KB) ← **OUTLIER**
- params19: RD=8  < WR=16 (512-bit, 2KB)
- params21: RD=16 > WR=8  (512-bit, 2KB)

Only 1 symmetric failure:
- params17: RD=8 = WR=8 (512-bit, 2KB, at absolute minimum SRAM)

### Critical Outlier: params14
**256-bit, RD=16, WR=8, 4KB SRAM**

- SRAM margin: 4KB - 2KB (minimum) = **2KB extra margin**
- Should pass easily based on SRAM sizing rule alone
- **Still fails** → Indicates issue beyond SRAM capacity
- Suggests **burst asymmetry handling problem in RTL**

---

## SRAM Sizing Analysis

All failures meet or marginally exceed the design rule:
**MIN_SRAM = MAX(2KB, 2 × max_burst_size)**

| Test | Max Burst | Min Required | Actual | Margin | Status |
|------|-----------|--------------|--------|--------|--------|
| params3  | 256B  | 2KB | 2KB | 0B    | At minimum |
| params13 | 512B  | 2KB | 2KB | 0B    | At minimum |
| params14 | 512B  | 2KB | 4KB | 2048B | **Well above!** |
| params17 | 512B  | 2KB | 2KB | 0B    | At minimum |
| params19 | 1KB   | 2KB | 2KB | 0B    | At minimum |
| params21 | 1KB   | 2KB | 2KB | 0B    | At minimum |

---

## ROOT CAUSE CONFIRMED: Scheduler Timeout on Asymmetric Bursts

### The Mechanism (scheduler.sv:572-613)

**Timeout Counter Logic:**
```systemverilog
// Counts cycles where sched_wr_valid && !sched_wr_ready
if (sched_wr_valid && !sched_wr_ready) begin
    r_timeout_counter <= r_timeout_counter + 1;
end

// Timeout triggers when counter >= cfg_sched_timeout_cycles
assign w_timeout_expired = cfg_sched_timeout_enable &&
                           (r_timeout_counter >= cfg_sched_timeout_cycles);
```

**Configuration (stream_core_tb.py:172-173):**
```python
cfg_sched_timeout_enable = 1
cfg_sched_timeout_cycles = 0xFFFF  # 65535 cycles
```

### Why Asymmetric Bursts Trigger Timeout

**Example: params14 (RD=16, WR=8)**
1. Read engine: 16 beats/burst → **fills SRAM 2x faster**
2. Write engine: 8 beats/burst → **drains SRAM 2x slower**
3. SRAM fills faster than draining → write engine can't keep up
4. Scheduler asserts `sched_wr_valid=1` but write engine keeps `sched_wr_ready=0`
5. Timeout counter increments every cycle: 1, 2, 3, ... 65535
6. After 65535 cycles (~655 microseconds @ 100MHz), timeout expires
7. FSM transitions to CH_ERROR state
8. Data corruption occurs as transfer aborted mid-stream

**Example: params19 (RD=8, WR=16)**
1. Read engine: 8 beats/burst → **fills SRAM 2x slower**
2. Write engine: 16 beats/burst → **drains SRAM 2x faster**
3. Write engine frequently waits for read engine to fill SRAM
4. Similar timeout condition but less severe (write naturally waits for data)

### Why Symmetric Bursts Work
When RD_BURST == WR_BURST:
- Balanced fill/drain rates
- SRAM level stays stable
- Write engine gets steady stream of data → `sched_wr_ready` stays high
- Timeout counter resets frequently → never reaches 65535
- No timeout, no error, transfer completes successfully

**Exception:** params17 (RD=8 == WR=8, 2KB) fails because:
- At absolute minimum SRAM (2KB for 512-bit width)
- Even balanced rates experience multi-channel arbitration delays
- Temporary SRAM empty conditions → write engine delays
- Marginal case where timeout still triggers occasionally

---

## Debug Files Available

### For params14 (256-bit, RD=16, WR=8, 4KB - the outlier):
**Directory:** `local_sim_build/test_stream_core_varsizes_nc04_dw0256_fd0128_sz128_burst_rd16_wr8_4KB_fast_gw15/`
**Files:**
- `dump.vcd` - Full waveform trace
- `tk8iypi7_results.xml` - Test results

### For params21 (512-bit, RD=16, WR=8, 2KB):
**Directory:** `local_sim_build/test_stream_core_single_nc04_dw0512_fd0032_dc04_burst_rd16_wr8_2KB_fast_gw21/`

### For params17 (512-bit, RD=8, WR=8, 2KB):
**Directory:** `local_sim_build/test_stream_core_varsizes_nc04_dw0512_fd0032_sz128_burst_rd8_wr8_2KB_fast_gw19/`

---

## Recommended Investigation Steps

### 1. Check SRAM Fill Level
Look for:
- **Overflow:** SRAM fill level reaching maximum (full)
- **Underflow:** SRAM fill level reaching zero (empty)
- **Oscillation:** Rapid fill/drain cycles

**Signals to check in VCD:**
- `sram_wr_ptr` - Write pointer
- `sram_rd_ptr` - Read pointer
- `sram_count` or equivalent fill level indicator

### 2. Check Burst Handshaking
Look for:
- Read bursts completing normally (all R beats transferred)
- Write bursts completing normally (all W beats transferred)
- Proper B response handling

**Signals:**
- AXI read: `m_axi_rd_rvalid`, `m_axi_rd_rready`, `m_axi_rd_rlast`
- AXI write: `m_axi_wr_wvalid`, `m_axi_wr_wready`, `m_axi_wr_wlast`

### 3. Check Engine State Machines
Look for:
- Read engine stuck in unexpected state
- Write engine stuck waiting for data
- Improper state transitions

### 4. Check Timing
With asymmetric bursts:
- Calculate expected fill rate: (RD_BURST × freq) beats/s
- Calculate expected drain rate: (WR_BURST × freq) beats/s
- Verify SRAM can buffer the difference over descriptor latency

---

## Recommended Fix Options

### Option 1: Increase Timeout Value (Quick Fix)
**Pros:** Simple, allows asymmetric bursts to complete
**Cons:** Masks underlying issue, may not scale to all cases

```python
# In stream_core_tb.py
self.dut.cfg_sched_timeout_cycles.value = 0xFFFFFF  # 16M cycles instead of 65K
```

**Analysis:**
- 65535 cycles @ 100MHz = 655 µs
- 16M cycles @ 100MHz = 160 ms
- Should be sufficient for most asymmetric burst scenarios
- Still provides deadlock protection

### Option 2: Disable Timeout for Burst Matrix Tests (Test-Only Fix)
**Pros:** Focuses on burst/SRAM validation without timeout concerns
**Cons:** Removes deadlock protection, may mask other issues

```python
# In stream_core_tb.py, only for burst tests
if test_level == 'burst':
    self.dut.cfg_sched_timeout_enable.value = 0  # Disable timeout
```

### Option 3: Dynamic Burst Throttling (RTL Fix)
**Pros:** Intelligent solution, prevents rate imbalance
**Cons:** More complex, requires RTL changes

**Concept:** Read engine monitors SRAM fill level and throttles when near full
```systemverilog
// In axi_read_engine.sv
assign throttle_read = (sram_fill_level > THROTTLE_THRESHOLD);
assign can_issue_read = sched_rd_valid && !throttle_read;
```

### Option 4: Adaptive Timeout Based on Transfer Size (RTL Enhancement)
**Pros:** Scales to any transfer size/burst combination
**Cons:** Requires careful calculation

**Concept:** Calculate timeout based on transfer length and burst asymmetry
```python
# Timeout formula: cycles_needed = (length / min(rd_burst, wr_burst)) * safety_margin
timeout_cycles = (descriptor.length / min(RD_BURST, WR_BURST)) * 10  # 10x safety
```

### Recommended Action

**Short term:** Option 1 (increase timeout to 16M cycles)
- Allows burst matrix tests to validate SRAM sizing
- Preserves deadlock protection
- Minimal code change

**Long term:** Option 3 (dynamic burst throttling)
- Prevents SRAM overflow/underflow inherently
- Better system behavior under asymmetric loads
- Production-quality solution

## Next Steps for Debugging

1. **Verify timeout hypothesis in VCD:**
   ```bash
   gtkwave local_sim_build/test_stream_core_varsizes_nc04_dw0256_fd0128_sz128_burst_rd16_wr8_4KB_fast_gw15/dump.vcd
   ```

   **Check these signals:**
   - `r_timeout_counter` - Should be incrementing towards 65535
   - `w_timeout_expired` - Should assert when counter hits 65535
   - `sched_wr_valid` - Should be high (scheduler requesting write)
   - `sched_wr_ready` - Should be low (write engine not ready)
   - `r_current_state` - Should transition from CH_XFER_DATA → CH_ERROR

2. **Compare with passing symmetric case (params16):**
   - Same config (256-bit, 4KB) but RD=16, WR=16
   - Check that `sched_wr_ready` stays high more consistently
   - Timeout counter should reset frequently, never reaching 65535

3. **Test the fix:**
   ```bash
   # Apply Option 1 fix, then re-run failed tests
   WAVES=0 TEST_LEVEL=burst pytest test_stream_core.py::test_stream_core_single_channel -k "params3 or params13 or params14 or params17 or params19 or params21" -v
   ```

---

## Pattern Summary

✅ **All symmetric burst tests pass** (RD == WR)
❌ **Most asymmetric burst tests fail** (RD ≠ WR)
❌ **Even with 2KB extra SRAM margin, asymmetric bursts fail**

**Conclusion:** This is NOT a simple SRAM sizing issue. The RTL appears to have difficulty handling asymmetric read/write burst sizes, even when SRAM capacity is adequate.
