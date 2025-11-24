# 8259 PIC Debug Session - 2025-11-17

## Summary

Debugging interrupt delivery failure in 8259 PIC. Tests 3, 4, and 5 fail with interrupt delivery issues, while tests 1, 2, and 6 pass.

---

## Root Causes Identified and Fixed

### 1. cfg_init_mode Bug (**CRITICAL BUG - FIXED**)

**Problem:** Testbench was setting `cfg_init_mode = 1` during initialization and never clearing it.

**Impact:** RTL code at [pic_8259_core.sv:157-159](file://pic_8259_core.sv#L157) causes PIC to return to INIT_IDLE state when cfg_init_mode is set:

```systemverilog
INIT_COMPLETE: begin
    // Stay in complete state unless re-initialized
    if (icw1_wr) begin
        r_init_state <= INIT_WAIT_ICW2;
    end else if (cfg_init_mode) begin
        // Manual return to init mode via config register
        r_init_state <= INIT_IDLE;  ← BUG: PIC goes back to INIT_IDLE!
    end
end
```

When `r_init_state != INIT_COMPLETE`, IRR is not updated [pic_8259_core.sv:251](file://pic_8259_core.sv#L251).

**Fix:** Changed `initialize_pic()` to set `cfg_init_mode = 0`:

```python
# OLD: await self.write_register(PIC8259RegisterMap.PIC_CONFIG, 0x00000007)
# NEW:
await self.write_register(PIC8259RegisterMap.PIC_CONFIG, 0x00000001)  # pic_enable=1, init_mode=0
```

**File:** [pic_8259_tb.py:393](file:///mnt/data/github/rtldesignsherpa/projects/components/retro_legacy_blocks/dv/tbclasses/pic_8259/pic_8259_tb.py#L393)

---

### 2. APB Register Write Timing Issues (**FIXED**)

**Problem:** Register writes (IMR, ICW1-4, EOI) were followed by insufficient wait cycles for APB transaction to complete and propagate to core.

**Impact:** Waveform analysis showed `r_imr = 0xFD` when test expected `0xDB` because IRQ was pulsed before IMR write completed.

**Fix:** Added 5-10 cycle waits after all register writes:

- `set_imr()`: Added 5-cycle wait after IMR write [pic_8259_tb.py:442](file:///mnt/data/github/rtldesignsherpa/projects/components/retro_legacy_blocks/dv/tbclasses/pic_8259/pic_8259_tb.py#L442)
- `initialize_pic()`: Increased waits from 2 to 5 cycles after each ICW write [pic_8259_tb.py:405,409,418](file:///mnt/data/github/rtldesignsherpa/projects/components/retro_legacy_blocks/dv/tbclasses/pic_8259/pic_8259_tb.py#L405)
- `send_eoi()`: Increased wait from 2 to 5 cycles [pic_8259_tb.py:466](file:///mnt/data/github/rtldesignsherpa/projects/components/retro_legacy_blocks/dv/tbclasses/pic_8259/pic_8259_tb.py#L466)
- Added 10-cycle wait after ICW4 before reading status [pic_8259_tb.py:418](file:///mnt/data/github/rtldesignsherpa/projects/components/retro_legacy_blocks/dv/tbclasses/pic_8259/pic_8259_tb.py#L418)
- Added 10-cycle wait at end of initialization [pic_8259_tb.py:430](file:///mnt/data/github/rtldesignsherpa/projects/components/retro_legacy_blocks/dv/tbclasses/pic_8259/pic_8259_tb.py#L430)

---

### 3. IRQ Signal Propagation (**ATTEMPTED FIX**)

**Problem:** `assert_irq()` and `deassert_irq()` were setting `dut.irq_in.value` without waiting for signal propagation.

**Fix:** Added 1-cycle wait after signal assignment:

```python
self.dut.irq_in.value = new_value
await self.wait_clocks('pclk', 1)  # Wait for signal to propagate
```

**Files:** [pic_8259_tb.py:293,310](file:///mnt/data/github/rtldesignsherpa/projects/components/retro_legacy_blocks/dv/tbclasses/pic_8259/pic_8259_tb.py#L293)

---

## Remaining Issue

**Status:** Tests 3, 4, 5 still fail with:

```
ERROR: IRR[0] not set after IRQ0 assertion: IRR=0x00
ERROR: INT not asserted after unmasking IRQ1
ERROR: INT not asserted for multiple IRQs
```

**Symptom:** IRR remains 0x00 after IRQ is pulsed, suggesting IRQ is not being captured.

**IRR Update Conditions** [pic_8259_core.sv:248-262](file://pic_8259_core.sv#L248):

```systemverilog
always_ff @(posedge clk) begin
    if (rst) begin
        r_irr <= 8'h00;
    end else if (!cfg_pic_enable) begin
        r_irr <= 8'h00;  ← IRR cleared if PIC disabled!
    end else if (r_init_state == INIT_COMPLETE) begin
        r_irr <= r_irr | w_irq_trigger;  ← IRR only updated if INIT_COMPLETE
        if (int_output && !cfg_aeoi) begin
            r_irr[highest_irq_comb] <= 1'b0;
        end
    end
end
```

For IRR to be set, ALL of these must be true:
1. ✅ NOT in reset
2. ❓ `cfg_pic_enable = 1` (else IRR gets cleared)
3. ❓ `r_init_state == INIT_COMPLETE` (else IRR not updated)
4. ❓ `w_irq_trigger` has a bit set

**Edge Detection Logic** [pic_8259_core.sv:182](file://pic_8259_core.sv#L182):

```systemverilog
assign w_irq_trigger = cfg_ltim ? irq_in : (irq_in & ~r_irq_last);
```

In edge-triggered mode (cfg_ltim=0): `w_irq_trigger = irq_in & ~r_irq_last`

---

## Waveform Analysis Required

**VCD Location:** `projects/components/retro_legacy_blocks/dv/tests/local_sim_build/test_apb_pic_8259_test_pic_8259_basic/dump.vcd`

**Critical Signals to Check:**

### Initialization State
```
u_pic_core.r_init_state[2:0]     # Should be 4 (INIT_COMPLETE) after ICW4 write
u_pic_core.cfg_pic_enable         # Should be 1 throughout
u_pic_core.cfg_ltim               # Should be 0 (edge-triggered)
```

### IRQ0 Test Sequence (around 2840ns based on error timestamp)
```
irq_in[0]                         # Should pulse HIGH for 10+ cycles
u_pic_core.r_irq_last[0]          # Should follow irq_in with 1-cycle delay
u_pic_core.w_irq_trigger[0]       # Should pulse HIGH for 1 cycle on rising edge
u_pic_core.r_irr[0]               # Should set to 1 and stay
u_pic_core.r_imr[0]               # Should be 0 (unmasked) - wrote 0xFE
u_pic_core.w_pending_irqs[0]      # Should be 1 when IRR[0]=1 and IMR[0]=0
u_pic_core.int_output             # Should assert when pending_irqs != 0
```

### Timeline Analysis
1. **T0:** Test completes initialization, reads status = 1 (init_complete)
2. **T+waits:** Test writes IMR = 0xFE, waits 5+2 = 7 cycles
3. **T+IRQ:** Test pulses IRQ0 for 10 cycles
4. **T+check:** Test reads IRR, expects 0x01, sees 0x00 ← **FAILURE**

### Possible Causes

**Hypothesis A: r_init_state Returns to INIT_IDLE**
- Even after cfg_init_mode fix, state machine may transition back
- Check: Does `r_init_state` stay at 4 (INIT_COMPLETE) during IRQ pulse?
- If NO: State machine bug or configuration issue

**Hypothesis B: cfg_pic_enable Glitches or Clears**
- IRR gets cleared if cfg_pic_enable goes to 0 (line 248-250)
- Check: Does `cfg_pic_enable` stay HIGH from init through IRQ pulse?
- If NO: Configuration register issue

**Hypothesis C: Edge Detection Not Working**
- w_irq_trigger should pulse for 1 cycle on irq_in rising edge
- Check: Does `w_irq_trigger[0]` pulse when `irq_in[0]` goes 0→1?
- If NO: Edge detection logic bug or cfg_ltim wrong

**Hypothesis D: IRQ Signal Not Reaching Core**
- Testbench may not be driving irq_in properly
- Check: Does top-level `irq_in[0]` actually go HIGH?
- If NO: Signal connection issue in testbench

---

## Files Modified

### Testbench Files
- [pic_8259_tb.py](file:///mnt/data/github/rtldesignsherpa/projects/components/retro_legacy_blocks/dv/tbclasses/pic_8259/pic_8259_tb.py)
  - Line 393: Fixed cfg_init_mode = 0 (was 1)
  - Line 405, 409, 418: Increased ICW wait times to 5 cycles
  - Line 418: Increased wait after ICW4 to 10 cycles
  - Line 430: Added 10-cycle wait after init complete
  - Line 442: Added 5-cycle wait in set_imr()
  - Line 466: Increased EOI wait to 5 cycles
  - Line 293, 310: Added 1-cycle wait after IRQ signal assignments

---

## Next Steps

1. **Open waveform in GTKWave:**
   ```bash
   gtkwave projects/components/retro_legacy_blocks/dv/tests/local_sim_build/test_apb_pic_8259_test_pic_8259_basic/dump.vcd &
   ```

2. **Add signals from "Critical Signals to Check" section above**

3. **Navigate to timestamp ~2840ns** (when "IRR[0] not set" error occurs)

4. **Answer these questions:**
   - Is `r_init_state == 4` when IRQ0 is pulsed?
   - Is `cfg_pic_enable == 1` when IRQ0 is pulsed?
   - Does `irq_in[0]` actually go HIGH?
   - Does `w_irq_trigger[0]` pulse?
   - Does `r_irr[0]` ever set to 1?

5. **Based on waveform, identify which condition fails**

6. **Fix the root cause** (likely RTL bug or testbench signal connection issue)

---

## Test Status

```
✅ PASSING (3/6):
- Test 1: Register Access
- Test 2: PIC Initialization
- Test 6: EOI Handling

❌ FAILING (3/6):
- Test 3: Single IRQ Handling
- Test 4: IRQ Masking
- Test 5: Multiple IRQ Priority

All failures have same root cause: IRR not being set when IRQ is pulsed.
```

---

## Useful References

- [PIC 8259 Core RTL](file:///mnt/data/github/rtldesignsherpa/projects/components/retro_legacy_blocks/rtl/pic_8259/pic_8259_core.sv)
- [GTKWave Signal List](file:///mnt/data/github/rtldesignsherpa/projects/components/retro_legacy_blocks/rtl/pic_8259/PIC_GTKWAVE_SIGNAL_LIST.txt)
- [Interrupt Delivery Debug Guide](file:///mnt/data/github/rtldesignsherpa/projects/components/retro_legacy_blocks/rtl/pic_8259/INTERRUPT_DELIVERY_DEBUG.md)
- [RLB Debug Status](file:///mnt/data/github/rtldesignsherpa/projects/components/retro_legacy_blocks/RLB_DEBUG_STATUS_2025-11-16.md)

---

**Session End:** 2025-11-17
**Next Action:** Waveform analysis required to identify why IRR is not being set
