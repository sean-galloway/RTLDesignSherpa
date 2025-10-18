# PeakRDL Integration Status for HPET

**Date:** 2025-10-16
**Status:** In Progress - External Register Approach

## Overview

Integrating PeakRDL-generated register block to replace hand-coded `hpet_config_regs.sv` implementation.

## Architecture

```
APB Interface → peakrdl_to_cmdrsp → hpet_regs (PeakRDL) → hpet_config_regs (wrapper) → hpet_core
```

### Key Components:
1. **hpet_regs.rdl** - SystemRDL specification
2. **hpet_regs.sv** - PeakRDL-generated register block
3. **hpet_regs_pkg.sv** - Generated package with hwif types
4. **hpet_config_regs.sv** - Wrapper mapping hwif ↔ hpet_core
5. **peakrdl_to_cmdrsp.sv** - Protocol adapter

## Current Approach: External Registers

### Counter Registers (HPET_COUNTER_LO/HI)

**Problem:** Counter maintained internally by HPET core, not by register block.
**Requirement:**
- SW reads must return live counter value from `counter_rdata`
- SW writes must initialize counter via `counter_write` pulse

**Solution:** Use PeakRDL `external` register type:
```systemrdl
external reg {
    field {
        sw = rw;
        hw = rw;
    } counter_lo[31:0];
} HPET_COUNTER_LO @ 0x010;
```

**Generated Interface:**
```systemverilog
// hwif_in - wrapper drives these
hwif_in.HPET_COUNTER_LO.rd_ack     // Always 1'b1 (ready)
hwif_in.HPET_COUNTER_LO.rd_data    // counter_rdata[31:0]
hwif_in.HPET_COUNTER_LO.wr_ack     // Assert when write detected

// hwif_out - PeakRDL drives these
hwif_out.HPET_COUNTER_LO.req       // Asserted for read or write
hwif_out.HPET_COUNTER_LO.req_is_wr // 1=write, 0=read
hwif_out.HPET_COUNTER_LO.wr_data   // Write data (valid when req_is_wr=1)
```

### Interrupt Status Register

**Semantics:** `hwset` with W1C (Write-1-to-Clear)
- HW pulses `hwset` to set bits
- SW writes 1 to clear via `woclr`

```systemrdl
field {
    sw = rw;
    onwrite = woclr;
    hwset;
} timer_int_status[NUM_TIMERS-1:0];
```

## Implementation Details

### hpet_config_regs.sv Wrapper Logic

#### Counter Read Path
```systemverilog
// Always acknowledge reads, return live counter value
assign hwif_in.HPET_COUNTER_LO.rd_ack = 1'b1;
assign hwif_in.HPET_COUNTER_LO.rd_data.counter_lo = counter_rdata[31:0];

assign hwif_in.HPET_COUNTER_HI.rd_ack = 1'b1;
assign hwif_in.HPET_COUNTER_HI.rd_data.counter_hi = counter_rdata[63:32];
```

#### Counter Write Path
```systemverilog
// Detect write requests
logic counter_lo_write = hwif_out.HPET_COUNTER_LO.req && hwif_out.HPET_COUNTER_LO.req_is_wr;
logic counter_hi_write = hwif_out.HPET_COUNTER_HI.req && hwif_out.HPET_COUNTER_HI.req_is_wr;

// Acknowledge writes
assign hwif_in.HPET_COUNTER_LO.wr_ack = counter_lo_write;
assign hwif_in.HPET_COUNTER_HI.wr_ack = counter_hi_write;

// Pulse counter_write on any write
assign counter_write = counter_lo_write || counter_hi_write;

// Combine write data: written half + preserved half
assign counter_wdata = {
    counter_hi_write ? hwif_out.HPET_COUNTER_HI.wr_data.counter_hi : counter_rdata[63:32],
    counter_lo_write ? hwif_out.HPET_COUNTER_LO.wr_data.counter_lo : counter_rdata[31:0]
};
```

#### Interrupt Status Path
```systemverilog
// Detect rising edge of HPET core interrupt to pulse hwset
logic [NUM_TIMERS-1:0] prev_timer_int_status;
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) prev_timer_int_status <= '0;
    else        prev_timer_int_status <= timer_int_status;
end

assign hwif_in.HPET_STATUS.timer_int_status.hwset =
    |(timer_int_status & ~prev_timer_int_status);
assign hwif_in.HPET_STATUS.timer_int_status.next = timer_int_status;

// Detect SW clearing (register falling edge)
logic [NUM_TIMERS-1:0] prev_status_reg_value;
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) prev_status_reg_value <= '0;
    else        prev_status_reg_value <= hwif_out.HPET_STATUS.timer_int_status.value;
end

assign timer_int_clear = prev_status_reg_value &
    ~hwif_out.HPET_STATUS.timer_int_status.value;
```

## Test Results

### Previous Working State (Before External Registers)
- ✅ Register Access: PASS
- ✅ Timer One-Shot: PASS
- ✅ Interrupt Clearing: PASS
- ❌ Counter Functionality: FAIL (counter not incrementing, writes not working)

### Current State (With External Registers)
- ❌ Register Access: FAIL
- ❌ Counter Functionality: FAIL
- ❌ Timer One-Shot: FAIL
- ❌ Interrupt Clearing: FAIL

**Regression:** All tests now failing with external register approach.

## Known Issues

### Issue 1: Counter Write Not Working
**Symptom:** Write 0x12345678, read back 0x00000036
**Status:** Investigating

**Hypotheses:**
1. Timing issue - `wr_data` only valid during `req` pulse
2. Counter write may need to be held for multiple cycles
3. External register protocol timing requirements not met

### Issue 2: Counter Not Incrementing
**Symptom:** Counter increments by 2 instead of ~100
**Status:** Unknown - may be related to write issue

### Issue 3: All Tests Regressed
**Symptom:** Even previously passing tests now fail
**Status:** External register approach may have broken basic functionality

## Comparison: Previous vs External Approach

### Previous Approach (sw=rw, hw=r)
```systemrdl
field {
    sw = rw;  // SW can read/write
    hw = r;   // HW reads stored value
} counter_lo[31:0];
```

**Issues:**
- ✅ Writes work
- ✅ Register access works
- ❌ Reads return stored value, not live counter
- ❌ Counter doesn't increment (HW can't update register)

### External Approach (external reg)
```systemrdl
external reg {
    field {
        sw = rw;
        hw = rw;
    } counter_lo[31:0];
} HPET_COUNTER_LO;
```

**Issues:**
- ❌ Writes not working (0x00000036 mystery value)
- ❌ All tests regressed
- ❓ Reads should work (return live value)
- ❓ Counter should increment (if reads work)

## Next Steps

### Option 1: Debug External Register Timing
- [ ] Add waveform inspection of external register signals
- [ ] Check `req`/`wr_data`/`wr_ack` timing
- [ ] Verify counter_write pulse timing to HPET core
- [ ] Add registered staging for write data if needed

### Option 2: Hybrid Approach
- [ ] Use external registers for counter (live reads)
- [ ] Add shadow registers to capture writes atomically
- [ ] Stage 64-bit writes (LO then HI)
- [ ] Only update HPET core on complete 64-bit write

### Option 3: Reconsider Architecture
- [ ] Could HPET core be modified to work with stored registers?
- [ ] Could we use PeakRDL callbacks/hooks?
- [ ] Is there a different SystemRDL semantic that fits better?

## Files Modified

### SystemRDL Definition
- `rtl/amba/components/hpet/peakrdl/hpet_regs.rdl`
  - Changed counter registers from `sw=rw, hw=r` to `external`

### Generated Files (Auto-updated)
- `rtl/amba/components/hpet/hpet_regs.sv`
- `rtl/amba/components/hpet/hpet_regs_pkg.sv`

### Wrapper
- `rtl/amba/components/hpet/hpet_config_regs.sv`
  - Updated counter handling for external register interface
  - Added read path: rd_ack, rd_data
  - Added write path: wr_ack detection, counter_write pulse, counter_wdata combining

### Tests
- `val/integ_amba/test_apb_hpet.py`
  - Added lint waivers: `-Wno-GENUNNAMED`, `-Wno-MULTIDRIVEN`, `-Wno-UNUSEDPARAM`

## References

### PeakRDL Documentation
- External registers: https://systemrdl-compiler.readthedocs.io/en/latest/rdl_spec/properties.html#external
- Field semantics: https://systemrdl-compiler.readthedocs.io/en/latest/rdl_spec/field_semantics.html
- Hardware interface: https://peakrdl-regblock.readthedocs.io/en/latest/

### Project Documentation
- HPET specification (Intel): docs/hpet_spec.pdf
- HPET PRD: rtl/amba/components/hpet/PRD.md

## Recommendations

**Immediate:** Focus on debugging why external registers broke everything, not just counter.

**Investigation Priority:**
1. Why did Register Access test fail? (Was passing before)
2. What is the 0x00000036 value? (54 decimal - specific meaning?)
3. Does external register protocol require different timing?

**Fallback:** If external registers prove too complex, revert to previous approach (sw=rw, hw=r) and document limitation that counter reads return stale value until next write.

---

**Last Updated:** 2025-10-16
**Author:** Claude Code (Automated PeakRDL Integration)
