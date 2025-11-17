# 8259 PIC Interrupt Delivery Debug Status

**Date:** 2025-11-16
**Status:** 3/6 tests passing
**Issue:** Interrupt delivery logic not working - `int_output` never asserts

---

## Progress Summary

### Test Results
**PASSING (3/6):**
- ✅ Register Access
- ✅ PIC Initialization (ICW sequence)
- ✅ EOI Handling (Specific and Non-specific EOI)

**FAILING (3/6):**
- ❌ Single IRQ Handling
- ❌ IRQ Masking
- ❌ Multiple IRQ Priority

All failures have same root cause: `int_output` never asserts when IRQ is triggered.

---

## Current Problem: Interrupt Delivery

### Symptoms
1. IRQs are pulsed correctly by testbench (10 cycles high, then low)
2. PIC initialization completes successfully (r_init_state == INIT_COMPLETE)
3. IMR is cleared (set to 0x00 or individual bits unmasked)
4. cfg_pic_enable is set to 1
5. But `int_output` never asserts
6. Tests timeout waiting for interrupt delivery

### What Should Happen (Per Spec)

1. IRQ input pulsed → edge detection → `w_irq_trigger[i]` = 1
2. Trigger sets IRR → `r_irr[i]` = 1
3. IRR bit anded with ~IMR → pending interrupt
4. Pending interrupt → `int_output` = 1
5. Test reads INT and sends EOI

### Signal Chain to Verify

```
irq_in[3]
  → irq_last[3] (1 cycle delay)
  → w_irq_trigger[3] (edge: irq_in & ~irq_last, or level: irq_in)
  → r_irr[3] (set on w_irq_trigger, clear when moves to ISR)
  → w_pending_irqs[3] (= r_irr & ~r_imr & ~r_isr, or r_irr & ~r_imr in special mask mode)
  → int_output (= init_complete && pic_enable && |w_pending_irqs)
```

### Files Involved

**`pic_8259_core.sv`** (Core Logic):
- Lines 172-178: Edge detection (irq_last register)
- Lines 180-182: Trigger signal generation
- Lines 244-263: IRR management (set on trigger, clear on move to ISR)
- Lines 269-301: ISR management (set on int_output, clear on EOI)
- Lines 307-315: IMR management (mask register)
- Lines 375-389: INT output generation ← **CRITICAL**

**Key Logic:**
```systemverilog
// Line 182: Edge vs level trigger
assign w_irq_trigger = cfg_ltim ? irq_in : (irq_in & ~r_irq_last);

// Lines 256: Set IRR on trigger
r_irr <= r_irr | w_irq_trigger;

// Lines 259-261: Clear IRR when moves to ISR
if (int_output && !cfg_aeoi) begin
    r_irr[highest_irq_comb] <= 1'b0;
end

// Lines 381-389: INT output (THE PROBLEM AREA)
assign w_pending_irqs = r_special_mask_mode ?
                        (r_irr & ~r_imr) :
                        (r_irr & ~r_imr & ~r_isr);

assign int_output = (r_init_state == INIT_COMPLETE) &&
                    cfg_pic_enable &&
                    (|w_pending_irqs);
```

---

## Debugging Approaches to Try

### 1. Waveform Analysis (HIGHEST PRIORITY)

VCD available at:
```
/mnt/data/github/rtldesignsherpa/projects/components/retro_legacy_blocks/dv/tests/local_sim_build/test_apb_pic_8259_test_pic_8259_basic/dump.vcd
```

**Key signals to trace for IRQ3 test:**
- `irq_in[3]` - Should pulse high for 10 cycles
- `u_core.r_irq_last[3]` - Delayed version of irq_in
- `u_core.w_irq_trigger[3]` - Should pulse for 1 cycle (edge) or follow input (level)
- `u_core.r_irr[3]` - Should set and stay high until moved to ISR
- `u_core.r_imr[3]` - Should be 0 (unmasked)
- `u_core.r_isr[3]` - Should be 0 initially
- `u_core.w_pending_irqs[3]` - Should be 1 when r_irr[3] && !r_imr[3] && !r_isr[3]
- `u_core.r_init_state` - Should be INIT_COMPLETE (3'd4)
- `u_core.cfg_pic_enable` - Should be 1
- `u_core.int_output` - Should assert when pending_irqs != 0
- `int_output` - Top-level INT signal

### 2. Check Configuration Propagation

Verify that configuration signals reach core correctly:

```systemverilog
// In waveform, after initialization:
u_pic.u_core.cfg_pic_enable      // Should be 1
u_pic.u_core.cfg_ltim             // Should be 0 (edge-triggered)
u_pic.u_core.cfg_aeoi             // Should be 0 (no auto-EOI)
u_pic.u_core.r_init_state         // Should be INIT_COMPLETE (4)
u_pic.u_core.r_imr                // Should be 0x00 or specific bits clear
```

### 3. Possible Root Causes

**Hypothesis A: Initialization Not Complete**
- r_init_state stuck in intermediate state
- init_complete signal not propagating
- cfg_pic_enable not being set
- **Solution:** Check waveform for init_state transitions

**Hypothesis B: Edge Detection Not Working**
- Edge-triggered mode: w_irq_trigger = irq_in & ~r_irq_last
- If r_irq_last not updating, edge never detected
- If clock not running during IRQ pulse, edge missed
- **Solution:** Check r_irq_last updates, verify IRQ pulse timing

**Hypothesis C: IRR Not Setting**
- Trigger detected but r_irr not setting
- Condition `r_init_state == INIT_COMPLETE` may be false
- Condition `!cfg_pic_enable` may be true
- **Solution:** Check enable conditions in waveform

**Hypothesis D: Pending IRQ Calculation Wrong**
- w_pending_irqs = r_irr & ~r_imr & ~r_isr
- If ANY bit in calculation wrong, pending_irqs = 0
- **Solution:** Check each operand in waveform

**Hypothesis E: Timing Issue**
- IRQ pulsed before initialization complete
- Test writes config then immediately pulses IRQ
- Config may not propagate before IRQ
- **Solution:** Add delay between init and IRQ pulse

### 4. Quick Tests to Run

**Test 1: Check if IRR ever sets**
Add logging to read IRR after IRQ pulse:
```python
# After IRQ pulse
irr = await tb.read_apb_register(PIC8259RegisterMap.IRR)
self.log.info(f"IRR after pulse = 0x{irr:02X}")
```

**Test 2: Check if init is complete**
Read status before IRQ:
```python
status = await tb.read_apb_register(PIC8259RegisterMap.STATUS)
self.log.info(f"Init complete = {status & 0x01}")
```

**Test 3: Increase wait time**
Change test to wait 50 cycles instead of 20:
```python
int_asserted = await self.tb.wait_for_interrupt(timeout_cycles=50)
```

**Test 4: Try level-triggered mode**
Change initialization to use level-triggered (cfg_ltim = 1):
```python
await tb.initialize_pic(vector_base=0x20, edge_mode=False)  # Level mode
```

---

## Test Configuration Details

**Test 3 (Single IRQ Handling):**
- IRQ: 3
- Vector base: 0x20
- Trigger mode: Edge (cfg_ltim=0)
- Auto-EOI: False
- IMR: 0xF7 (IRQ3 unmasked, all others masked)

**IRQ Pulse:**
- Assert for 10 cycles
- Then deassert
- Wait 20 cycles for delivery

**Expected Timeline:**
- Cycle 0: IRQ3 asserted (irq_in[3] = 1)
- Cycle 1: r_irq_last[3] = 1 (delayed)
- Cycle 2: w_irq_trigger[3] = 0 (no edge yet, both high)
- Cycle 10: IRQ3 deasserted (irq_in[3] = 0)
- Cycle 11: Falling edge detected, but we use rising edge
- **ISSUE:** Edge-triggered uses RISING edge (irq_in & ~irq_last)
- Rising edge occurs on Cycle 0→1 transition
- Should trigger on cycle 1!

---

## Key Differences from IOAPIC

### Similar Issues
1. Both have interrupt delivery not working
2. Both have 3/6 tests passing (register access works)
3. Both fail on actual interrupt delivery tests

### Different Architecture
- **IOAPIC:** Complex state machine (IDLE → DELIVER → WAIT_EOI)
- **PIC:** Simple combinational INT output (no state machine)

### Different Trigger Logic
- **IOAPIC:** 3-stage synchronizer → polarity → edge detection → pending flag
- **PIC:** 1-cycle delay → edge/level detection → IRR register

### Simpler Debug
- PIC has fewer moving parts - easier to debug
- INT output is purely combinational from {init_state, enable, pending_irqs}
- If pending_irqs != 0 and conditions met, INT MUST assert

---

## Questions to Answer

1. Does `r_irr[3]` ever set to 1 in the waveform?
2. Does `w_irq_trigger[3]` pulse on the rising edge of irq_in[3]?
3. Is `r_init_state` == INIT_COMPLETE (4) when IRQ is pulsed?
4. Is `cfg_pic_enable` == 1?
5. Is `r_imr[3]` == 0 (unmasked)?
6. What is the value of `w_pending_irqs` after IRQ pulse?
7. Does `int_output` combinationally follow `w_pending_irqs`?

---

## Recommended Next Steps

1. **Open VCD in GTKWave** - Trace signal chain for IRQ3 test
2. **Identify exactly where signal flow breaks** - Which signal never toggles?
3. **Check configuration timing** - Is init complete before IRQ pulse?
4. **Compare with IOAPIC** - Same root cause across both blocks?
5. **Consider common issue** - Both use same testbench pattern, same APB infrastructure

---

## Potential Common Root Cause

**CRITICAL OBSERVATION:** Both IOAPIC and PIC have IDENTICAL failure pattern:
- Register access works (3 tests pass)
- Interrupt delivery fails (3 tests fail)

**Hypothesis: Testbench Issue?**
- Both use same APB BFM
- Both use same wait_for_interrupt() pattern
- Both use same IRQ pulse pattern
- **Could the IRQ signal not be reaching the DUT?**
- **Could the interrupt output not be monitored correctly?**

**Test: Check DUT signal connections**
```python
# In testbench, after pulse_irq(3):
dut_irq_in = self.dut.irq_in.value.integer
self.log.info(f"DUT sees irq_in = 0x{dut_irq_in:02X}")

dut_int_out = self.dut.int_output.value.integer
self.log.info(f"DUT int_output = {dut_int_out}")
```

---

**Priority:** HIGH
**Blocker:** Yes - blocks PIC completion
**Impact:** 3 of 6 tests failing, interrupt delivery non-functional
**Related:** IOAPIC has identical issue - may share root cause
