# Retro Legacy Blocks - Debug Status Summary

**Date:** 2025-11-16
**Session:** Continued from previous context overflow
**Focus:** IOAPIC and 8259 PIC interrupt delivery debugging

---

## Executive Summary

Two RLB blocks (IOAPIC and 8259 PIC) have identical interrupt delivery failure patterns:
- **Register access works** (3/3 tests passing each)
- **Interrupt delivery fails** (3/3 tests failing each)
- **Both have 3/6 overall test pass rate**

This suggests a potential common root cause that needs investigation via waveform analysis.

---

## Block Status Matrix

| Block | Tests Pass | Tests Fail | Status | Issue |
|-------|------------|------------|--------|-------|
| HPET | 5/6 (100%) | 0 | ✅ Complete | None |
| PIT 8254 | 6/6 (100%) | 0 | ✅ Complete | None |
| RTC | 6/6 (100%) | 0 | ✅ Complete | None |
| IOAPIC | 3/6 (50%) | 3 | 🔧 Debug | Interrupt delivery |
| 8259 PIC | 3/6 (50%) | 3 | 🔧 Debug | Interrupt delivery |
| SMBus | - | - | ❌ No tests | Blocked on interrupt debug |

---

## IOAPIC Status

### Working Tests ✅
1. Indirect Register Access (IOREGSEL/IOWIN mechanism)
2. Identification Registers (IOAPICID, IOAPICVER, IOAPICARB)
3. Redirection Table Access (24 IRQs × 64-bit entries)

### Failing Tests ❌
4. Edge-Triggered Interrupt Delivery
5. Interrupt Masking
6. Multiple IRQ Priority Resolution

### Root Cause
- `irq_out_valid` never asserts when IRQ is pulsed
- IRQ inputs correctly synchronized
- Redirection table configured correctly
- Mask bits cleared (interrupts enabled)
- But interrupt delivery state machine never transitions IDLE → DELIVER

### Major Fix Completed
✅ **Indirect Register Access Implementation** (CRITICAL FIX)
- PeakRDL does NOT auto-generate Intel's indirect access mechanism
- Implemented custom translation logic in `ioapic_config_regs.sv`:
  - IOREGSEL capture register (stores internal offset)
  - IOWIN address translation (maps to APB addresses)
  - Response path passthrough
- This fixed ALL register access tests (went from 0/6 to 3/6)

### Debug Resources
- **VCD File:** `/mnt/data/github/rtldesignsherpa/projects/components/retro_legacy_blocks/dv/tests/local_sim_build/test_apb_ioapic_test_ioapic_basic/dump.vcd`
- **Debug Guide:** `projects/components/retro_legacy_blocks/rtl/ioapic/INTERRUPT_DELIVERY_DEBUG.md`
- **Key Signals:**
  - `irq_in[2]` → IRQ input
  - `u_ioapic_core.irq_pending[2]` → Pending flag
  - `u_ioapic_core.delivery_state` → State machine
  - `irq_out_valid` → Interrupt output

### Next Steps
1. Open VCD in GTKWave
2. Trace signal chain for IRQ2 test
3. Identify where signal flow breaks
4. Check if `irq_pending[2]` ever sets
5. Check if state machine transitions

---

## 8259 PIC Status

### Working Tests ✅
1. Register Access (direct APB, no indirection needed)
2. PIC Initialization (ICW1-4 sequence)
3. EOI Handling (Specific and Non-specific EOI)

### Failing Tests ❌
4. Single IRQ Handling
5. IRQ Masking
6. Multiple IRQ Priority Resolution

### Root Cause
- `int_output` never asserts when IRQ is pulsed
- IRQ edge detection logic exists
- IMR (Interrupt Mask Register) cleared
- Initialization completes successfully
- But INT output remains low

### Debug Resources
- **VCD File:** `/mnt/data/github/rtldesignsherpa/projects/components/retro_legacy_blocks/dv/tests/local_sim_build/test_apb_pic_8259_test_pic_8259_basic/dump.vcd`
- **Debug Guide:** `projects/components/retro_legacy_blocks/rtl/pic_8259/INTERRUPT_DELIVERY_DEBUG.md`
- **Key Signals:**
  - `irq_in[3]` → IRQ input
  - `u_core.w_irq_trigger[3]` → Edge detection
  - `u_core.r_irr[3]` → Interrupt Request Register
  - `u_core.w_pending_irqs[3]` → Pending calculation
  - `u_core.int_output` → INT pin state

### INT Output Logic (Lines 387-389)
```systemverilog
assign int_output = (r_init_state == INIT_COMPLETE) &&
                    cfg_pic_enable &&
                    (|w_pending_irqs);
```

This is PURELY COMBINATIONAL - no state machine. If conditions are met, INT MUST assert.

### Next Steps
1. Open VCD in GTKWave
2. Trace signal chain for IRQ3 test
3. Check if `r_irr[3]` ever sets
4. Check if `w_irq_trigger[3]` pulses
5. Verify init_state == INIT_COMPLETE before IRQ
6. Verify cfg_pic_enable == 1

---

## Common Pattern Analysis

### Identical Failure Symptoms
Both IOAPIC and PIC have the exact same pattern:
- ✅ Register access works perfectly
- ✅ Initialization/configuration works
- ❌ Interrupt delivery completely non-functional

### Potential Common Causes

**Hypothesis 1: Testbench IRQ Signal Issue**
- Both use same testbench pattern
- Both use same `pulse_irq()` method
- Both use same `wait_for_interrupt()` method
- **Could IRQ signals not reach DUT?**
- **Could interrupt outputs not be monitored?**

**Hypothesis 2: Timing Issue**
- Configuration writes may not propagate before IRQ pulse
- Tests write config, immediately pulse IRQ
- No wait cycles between config and IRQ
- **Try adding 10-cycle delay after config**

**Hypothesis 3: Enable Signal Issue**
- Both have enable bits (cfg_pic_enable, ioapic_enable)
- Enable may not be set in testbench
- Enable may not propagate to core
- **Check enable signal in waveform**

**Hypothesis 4: Initialization Not Complete**
- Both have init sequences
- Initialization may appear complete in registers
- But core may not see init_complete signal
- **Check init status propagation**

### Recommended Debug Order

1. **Start with PIC** (simpler architecture)
   - No state machine - combinational INT output
   - Fewer signals to trace
   - Easier to isolate issue

2. **Check testbench signal connections**
   ```python
   # After pulse_irq(3):
   dut_irq = self.dut.irq_in.value.integer
   self.log.info(f"DUT irq_in = 0x{dut_irq:02X}")

   dut_int = self.dut.int_output.value
   self.log.info(f"DUT int_output = {dut_int}")
   ```

3. **Verify all enable conditions**
   - Is init complete?
   - Is block enabled?
   - Are masks cleared?
   - Is IRQ actually pulsing?

4. **If PIC works after fix, apply to IOAPIC**
   - Likely same root cause
   - Same fix pattern

---

## SMBus Status

**Current State:** RTL complete, no tests exist

**Decision:** Deferred pending interrupt delivery debug resolution

**Rationale:**
- SMBus has `smb_interrupt` output
- Will likely encounter same interrupt delivery issue
- Better to debug interrupt issues in IOAPIC/PIC first
- Then apply fixes to SMBus test creation

**SMBusHelper Already Exists:**
- High-level transaction API (write_byte_data, read_word_data, block_write, etc.)
- Uses RegisterMap class from CocoTBFramework
- Automatically generates APB transactions
- No need for full SMBus/I2C BFM - just need simple slave mock

**When Ready:**
- SMBus can follow UART-style pattern:
  ```python
  from SMBusHelper import SMBusHelper  # High-level API (exists)
  from SimpleSMBusSlaveMock import SimpleSMBusSlaveMock  # Need to create
  ```
- SimpleSMBusSlaveMock: ~100-200 lines to respond to SCL/SDA signals
- Not a full SMBus master BFM - hard work already done in SMBusHelper

---

## Files Modified This Session

### IOAPIC
- `projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_core.sv`
  - Line 131: Fixed unpacked array declaration for irq_remote_irr
  - Lines 216-223: Modified pending flag clear logic (still has bugs)

- `projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_config_regs.sv`
  - Lines 75-104: Added adapter/regblk signal split
  - Lines 139-148: IOREGSEL capture logic
  - Lines 150-193: IOWIN address translation logic (CRITICAL FIX)
  - Lines 195-202: Response path passthrough

- `projects/components/retro_legacy_blocks/dv/tbclasses/ioapic/ioapic_tb.py`
  - Lines 175-176, 221, 224, 484, 499-500, 514-516: Fixed signal name mismatches

### 8259 PIC
- No RTL modifications (interrupt delivery issue still under investigation)

### Documentation
- `projects/components/retro_legacy_blocks/rtl/ioapic/INTERRUPT_DELIVERY_DEBUG.md` (new)
- `projects/components/retro_legacy_blocks/rtl/pic_8259/INTERRUPT_DELIVERY_DEBUG.md` (new)
- `projects/components/retro_legacy_blocks/BLOCK_STATUS.md` (updated)

---

## Critical Observations

### What Works
1. **APB Infrastructure:** All register access works perfectly
2. **PeakRDL Integration:** Register generation working (after indirect access fix)
3. **Initialization:** Both blocks complete init sequences correctly
4. **Configuration:** Registers can be written and read back correctly
5. **EOI Logic:** PIC EOI handling works (proves some core logic functional)

### What Doesn't Work
1. **Interrupt Delivery:** Neither block generates interrupt output
2. **IRQ Processing:** IRQ inputs not being processed to outputs
3. **State Machines:** IOAPIC delivery state machine stuck in IDLE

### Key Insight
The fact that register access works but interrupt delivery doesn't suggests:
- **Not a compilation issue** (RTL compiles and runs)
- **Not a connection issue** (APB works)
- **Not a reset issue** (registers work)
- **Likely a signal propagation or timing issue in interrupt path**

---

## Recommended Tomorrow's Actions

### Priority 1: Debug PIC (Simpler)
1. Open `dump.vcd` in GTKWave
2. Add signals from debug guide
3. Trace IRQ3 signal chain
4. Find where signal flow stops
5. Fix root cause
6. Verify all 6 tests pass

### Priority 2: Apply Fix to IOAPIC
1. Use same debug methodology
2. Apply similar fix
3. Verify all 6 tests pass

### Priority 3: Create SMBus Tests
1. Only after interrupt delivery works
2. Follow RTC/PIT/HPET working patterns
3. Use SMBusHelper for transactions
4. Create SimpleSMBusSlaveMock (~200 lines)

---

## Questions for Waveform Analysis

### PIC (Start Here)
1. Does `irq_in[3]` pulse high for 10 cycles?
2. Does `r_irq_last[3]` follow with 1-cycle delay?
3. Does `w_irq_trigger[3]` pulse for 1 cycle?
4. Does `r_irr[3]` set and stay high?
5. Is `r_imr[3]` == 0?
6. Is `r_isr[3]` == 0?
7. What is `w_pending_irqs`?
8. Is `r_init_state` == INIT_COMPLETE (4)?
9. Is `cfg_pic_enable` == 1?
10. Does `int_output` follow combinational logic?

### IOAPIC (After PIC)
1. Does `irq_in[2]` pulse high for 10 cycles?
2. Does `irq_pending[2]` ever set?
3. Does `irq_selected_valid` ever assert?
4. What is `delivery_state` value?
5. Does `cfg_mask[2]` == 0?
6. Does `irq_out_valid` follow delivery_state?

---

## Additional Context

### Test Infrastructure Creation
This session successfully created complete test infrastructure for IOAPIC:
- Main testbench class with TBBase contract
- 6 comprehensive tests
- Test runner with Pattern B (CocoTB + Pytest)
- Pytest configuration

### Signal Naming Fixes
Fixed 6 signal name mismatches between testbench and DUT by reading actual RTL ports.

### Indirect Access Discovery
Major discovery that PeakRDL does NOT automatically implement Intel's IOREGSEL/IOWIN indirect access mechanism. This is likely a common pattern for other Intel-compatible blocks.

---

**Status:** Ready for waveform-based debugging
**Blockers:** None - VCD files available, debug guides complete
**Risk:** Medium - common failure pattern suggests systematic issue
**Confidence:** High that waveform analysis will reveal root cause
