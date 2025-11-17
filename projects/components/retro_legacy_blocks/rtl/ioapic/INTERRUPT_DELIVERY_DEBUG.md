# IOAPIC Interrupt Delivery Debug Status

**Date:** 2025-11-16
**Status:** 3/6 tests passing (was 0/6)
**Issue:** Interrupt delivery logic not working - `irq_out_valid` never asserts

---

## Progress Summary

### Fixed Issues ✅
1. **Indirect Register Access (IOREGSEL/IOWIN)** - COMPLETE
   - PeakRDL does not automatically implement Intel's indirect access
   - Added custom logic in `ioapic_config_regs.sv` (lines 134-202)
   - Captures writes to IOREGSEL (APB 0x00)
   - Translates IOWIN accesses (APB 0x04) to internal register addresses
   - Mapping: offset 0x00→0x08, 0x01→0x0C, 0x02→0x10, 0x10-0x3F→0x14+...

### Test Results
**PASSING (3/6):**
- ✅ Indirect Register Access
- ✅ Identification Registers (IOAPICVER returns 0x00170011 correctly)
- ✅ Redirection Table Access

**FAILING (3/6):**
- ❌ Edge-Triggered Interrupt Delivery
- ❌ Interrupt Masking
- ❌ Multiple IRQ Priority

All failures have same root cause: `irq_out_valid` never asserts.

---

## Current Problem: Interrupt Delivery

### Symptoms
1. IRQs are configured correctly (verified by register readback)
2. IRQs are pulsed by testbench (10 cycles high, then low)
3. `irq_out_ready` is set to 1 by testbench in `setup_components()`
4. But `irq_out_valid` never asserts within 20-cycle timeout
5. State machine never transitions from IDLE → DELIVER

### What Should Happen (Per Spec)
1. IRQ input → 3-stage synchronization → `irq_level`
2. Polarity handling → `irq_active`
3. Edge detection → `irq_edge_trigger` (rising edge)
4. Pending flag set → `irq_pending[i]` = 1
5. Eligibility check → `irq_eligible[i]` = `irq_pending[i]` && !`cfg_mask[i]`
6. Arbitration → Lowest IRQ selected, `irq_selected_valid` = 1
7. State machine → IDLE → DELIVER (when `irq_selected_valid`)
8. Output → `irq_out_valid` = 1 (when `delivery_state` == DELIVER)

### Signal Chain to Verify
```
irq_in[2]
  → irq_sync[0][2], irq_sync[1][2], irq_sync[2][2] (3 cycles)
  → irq_level[2]
  → irq_active[2] (with polarity=0, active = level)
  → irq_edge_rising[2] (irq_active & ~irq_active_prev)
  → irq_edge_trigger[2] (= irq_edge_rising)
  → irq_pending[2] (sets on edge, clears on delivery+ready)
  → irq_eligible[2] (= pending && !mask)
  → selected_irq = 2, irq_selected_valid = 1 (arbitration)
  → next_delivery_state = DELIVER (state machine)
  → delivery_state = DELIVER (next cycle)
  → irq_out_valid = 1 (output assign)
```

### Files Modified

**`ioapic_config_regs.sv`** (WORKING):
- Lines 75-104: Split adapter/regblk signals for indirection
- Lines 139-148: IOREGSEL capture logic
- Lines 150-193: IOWIN address translation logic
- Lines 195-202: Response path passthrough

**`ioapic_core.sv`** (ATTEMPTED FIXES - STILL BROKEN):
- Lines 216-223: Modified pending flag clear logic
  - Original: Cleared when `irq_selected_valid` && `delivery_state == IDLE`
  - Problem: Created combinational loop - pending cleared same cycle as selection
  - Current: Clear when `delivery_state == DELIVER` && `current_irq == i` && `irq_out_ready`
  - Still not working!

---

## Debugging Approaches to Try

### 1. Waveform Analysis (HIGHEST PRIORITY)
VCD available at:
```
/mnt/data/github/rtldesignsherpa/projects/components/retro_legacy_blocks/dv/tests/local_sim_build/test_apb_ioapic_test_ioapic_basic/dump.vcd
```

Key signals to trace for IRQ2 test:
- `irq_in[2]` - Should pulse high for 10 cycles
- `u_ioapic_core.irq_level[2]` - After sync (3 cycles delay)
- `u_ioapic_core.irq_active[2]` - After polarity
- `u_ioapic_core.irq_edge_trigger[2]` - Should pulse for 1 cycle on rising edge
- `u_ioapic_core.irq_pending[2]` - Should set and stay high until delivered
- `u_ioapic_core.cfg_mask[2]` - Should be 0 (enabled)
- `u_ioapic_core.irq_eligible[2]` - Should be 1 when pending && !mask
- `u_ioapic_core.irq_selected_valid` - Should be 1 when any eligible
- `u_ioapic_core.selected_irq` - Should be 2
- `u_ioapic_core.delivery_state` - Should transition IDLE→DELIVER
- `irq_out_valid` - Should assert when delivery_state == DELIVER

### 2. Check Configuration Propagation
Verify hwif signals are correctly mapped:
```bash
# In waveform, check when IRQ2 config is written (offset 0x14):
u_ioapic.u_config_regs.hwif_out.IOREDTBL[2].REDIR_LO.vector.value  # Should be 0x22
u_ioapic.u_config_regs.hwif_out.IOREDTBL[2].REDIR_LO.mask.value    # Should be 0
u_ioapic.u_config_regs.hwif_out.IOREDTBL[2].REDIR_LO.trigger_mode.value  # Should be 0

# Then check if these propagate to core:
u_ioapic.u_core.cfg_vector[2]       # Should be 0x22
u_ioapic.u_core.cfg_mask[2]         # Should be 0
u_ioapic.u_core.cfg_trigger_mode[2] # Should be 0
```

### 3. Possible Root Causes

**Hypothesis A: Timing Issue**
- Configuration writes may not be taking effect before IRQ pulse
- Test writes config then immediately pulses IRQ
- Need to check if `hwif_out` updates same cycle or next cycle after write
- Solution: Add delay between config write and IRQ pulse

**Hypothesis B: Pending Flag Logic Bug**
- Current clear condition may still have race condition
- Clearing on `delivery_state == DELIVER` but checking `current_irq`
- `current_irq` is only latched on IDLE→DELIVER transition (line 307)
- May need to hold pending flag until state returns to IDLE

**Hypothesis C: Arbitration Not Running**
- Combinational `always_comb` block may have synthesis issue
- `for (int j...)` loop may not synthesize correctly
- Consider changing to generate block with priority encoder

**Hypothesis D: Configuration Default Values**
- RDL spec shows `mask[16:16] = 1'b1` (default masked)
- PeakRDL may not be applying write correctly
- Check if write strobe is handling all bits

**Hypothesis E: Clock Domain Issue**
- `ioapic_core` might be on wrong clock domain
- Check `apb_ioapic.sv` clock routing with CDC_ENABLE=0
- Both config_regs and core should be on `pclk` when CDC disabled

### 4. Quick Tests to Run

**Test 1: Check if ANY signal in chain ever sets**
Add debug logging in testbench to read core signals via hierarchy:
```python
# After IRQ pulse, check pending flag
pending = dut.u_core.irq_pending.value
self.log.info(f"irq_pending = 0x{pending:06X}")
```

**Test 2: Increase wait time**
Change test to wait 50 cycles instead of 20:
```python
int_delivered = await self.tb.wait_for_interrupt(timeout_cycles=50)
```

**Test 3: Try different IRQ**
Test with IRQ0 instead of IRQ2 to rule out indexing issue.

**Test 4: Check without edge trigger**
Modify pending logic to set based on level instead of edge (temporarily):
```systemverilog
irq_pending[i] <= irq_active[i];  // Level instead of edge
```

---

## Recommended Next Steps

1. **Open VCD in GTKWave** - Trace signal chain for IRQ2 test
2. **Identify exactly where signal flow breaks** - Which signal never toggles?
3. **Check configuration timing** - Does `cfg_mask[2]` == 0 before IRQ pulse?
4. **Review pending flag logic** - May need different clear strategy
5. **Compare with working blocks** - Check HPET/PIT/RTC interrupt patterns

---

## Code Locations

**Key Files:**
- `ioapic_core.sv` - Interrupt logic (lines 200-395)
- `ioapic_config_regs.sv` - Register wrapper (lines 134-230)
- `ioapic_tb.py` - Testbench (lines 215-520 for IRQ methods)
- `ioapic_tests_basic.py` - Test 4 edge trigger (lines 221-289)

**Key Logic Blocks in `ioapic_core.sv`:**
- Lines 156-169: IRQ synchronization (3 stages)
- Lines 178-182: Polarity handling
- Lines 190-204: Edge detection
- Lines 210-231: Pending flag logic ← SUSPECT
- Lines 272-276: Eligibility check
- Lines 279-290: Priority arbitration ← SUSPECT
- Lines 297-349: Delivery state machine
- Lines 355-358: Output assignments

---

## Test Configuration Details

**Test 4 (Edge-Triggered Interrupt):**
- IRQ: 2
- Vector: 0x22
- Dest: 0x01
- Delivery mode: 0 (Fixed)
- Dest mode: 0 (Physical)
- Polarity: 0 (Active high)
- Trigger mode: 0 (Edge)
- Mask: 0 (Enabled)

**IRQ Pulse:**
- Assert for 10 cycles
- Then deassert
- Wait 20 cycles for delivery

**Expected Timeline:**
- Cycle 0: IRQ2 asserted
- Cycle 3-5: Edge detected (after sync)
- Cycle 4-6: Pending flag set
- Cycle 5-7: Arbitration selects IRQ2
- Cycle 6-8: State → DELIVER
- Cycle 7-9: `irq_out_valid` = 1 ← NEVER HAPPENS

---

## Questions to Answer Tomorrow

1. Does `irq_pending[2]` ever set to 1 in the waveform?
2. Does `cfg_mask[2]` read as 0 after configuration?
3. Does `irq_selected_valid` ever assert?
4. What is `delivery_state` doing - stuck in IDLE?
5. Is there a Verilator synthesis issue with the `for` loop in arbitration?

---

**Priority:** HIGH
**Blocker:** Yes - blocks IOAPIC completion
**Impact:** 3 of 6 tests failing, interrupt delivery non-functional
