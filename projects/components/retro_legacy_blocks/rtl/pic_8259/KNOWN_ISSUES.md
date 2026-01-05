<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# PIC 8259 Known Issues

**Last Updated:** 2025-11-16

---

## Issue #1: Missing INTA Cycle Support

**Status:** Open
**Priority:** High
**Affects:** IRQ handling, ISR updates
**Discovered:** 2025-11-16

### Description

The PIC 8259 core expects an INTA (Interrupt Acknowledge) cycle to move interrupts from the IRR (Interrupt Request Register) to the ISR (In-Service Register). Currently, the APB wrapper does not provide INTA cycle support, causing IRQ handling to fail.

### Root Cause

In [pic_8259_core.sv:259-261](pic_8259_core.sv#L259-L261):

```systemverilog
// Clear IRR bit when interrupt moves to ISR
if (int_output && !cfg_aeoi) begin
    r_irr[highest_irq_comb] <= 1'b0;
end
```

This logic clears the IRR bit when `int_output` is asserted, but without an INTA cycle:
- The IRQ never moves to ISR
- The IRR bit gets cleared anyway
- Subsequent IRQs cannot be captured

### Impact

**Test Results:** 3/6 passing (50%)

**Passing Tests:**
- Register Access
- PIC Initialization
- EOI Handling

**Failing Tests:**
- Single IRQ Handling - IRR not capturing IRQ inputs
- IRQ Masking - Cannot test masked vs unmasked IRQs
- Multiple IRQ Priority - Priority resolution requires working IRR

### Workaround

None available. The issue requires architectural changes to the RTL.

### Proposed Solutions

#### Option 1: Add INTA Signal to APB Interface

Add an INTA input signal to `apb_pic_8259`:

```systemverilog
module apb_pic_8259 (
    // ... existing ports ...
    input  wire        inta,  // Interrupt acknowledge
    output wire [7:0]  int_vector  // Interrupt vector output
);
```

**Pros:**
- Matches real 8259A behavior
- Explicit control from CPU/system

**Cons:**
- Requires APB master to generate INTA
- More complex integration

#### Option 2: Auto-Generate INTA Internally

Automatically generate INTA when INT is asserted and configuration register is read:

```systemverilog
// Auto-INTA on STATUS register read when INT is asserted
wire w_auto_inta = regblk_req && !regblk_req_is_wr &&
                   (regblk_addr == STATUS_ADDR) &&
                   int_output;
```

**Pros:**
- No interface changes needed
- Simpler integration
- APB-friendly approach

**Cons:**
- Deviates from real 8259A behavior
- May not work for all use cases

#### Option 3: Hybrid Approach

Provide both explicit INTA input and auto-INTA configuration:

```systemverilog
// CONFIG register bit: auto_inta_enable
// If auto_inta_enable: generate INTA on STATUS read
// If !auto_inta_enable: use external inta signal
```

**Pros:**
- Flexible for different use cases
- Backward compatible

**Cons:**
- Most complex to implement

### Recommended Solution

**Option 2 (Auto-Generate INTA)** is recommended for APB-based systems because:
1. APB is a simple slave-only protocol without CPU-style INTA cycles
2. Reading the STATUS register is a natural point to acknowledge interrupts
3. Simplifies integration with APB-based SoCs
4. The PIC is being used in a different context than original x86 systems

### Implementation Plan

1. Add `auto_inta_enable` bit to PIC_CONFIG register (default=1)
2. Generate `w_auto_inta` signal on STATUS register read when INT asserted
3. Pass `w_auto_inta` to pic_8259_core as `inta` input
4. Update pic_8259_core to use `inta` signal for IRR→ISR transfer
5. Update tests to read STATUS after INT assertion

### References

- Intel 8259A Datasheet: Interrupt Acknowledge Sequence
- pic_8259_core.sv: IRR/ISR management logic
- Test log: shows IRR=0x00 after IRQ pulse

---

## Issue #2: Auto-Reset Init Implementation

**Status:** Fixed
**Priority:** Medium
**Affects:** Initialization sequence
**Discovered:** 2025-11-16
**Fixed:** 2025-11-16

### Description

The `auto_reset_init` bit in PIC_CONFIG register was defined in the RDL but not implemented in the hardware logic.

### Fix Applied

Added hardware write logic in [pic_8259_config_regs.sv:200](pic_8259_config_regs.sv#L200):

```systemverilog
// When auto_reset_init is set and ICW4 is written, automatically clear init_mode
assign hwif_in.PIC_CONFIG.init_mode.next = (auto_reset_init && r_icw4_wr_ack) ? 1'b0 : hwif_out.PIC_CONFIG.init_mode.value;
```

This automatically clears `init_mode` after ICW4 is written when `auto_reset_init=1`.

### Verification

Initialization test now passes (STATUS register bit 0 = 1 after ICW sequence).

---

## Issue #3: Incorrect Init_Complete Bit Check

**Status:** Fixed
**Priority:** Low
**Affects:** Testbench
**Discovered:** 2025-11-16
**Fixed:** 2025-11-16

### Description

Testbench was checking bit 7 of STATUS register for init_complete, but the actual bit is bit 0 per the RDL specification.

### Fix Applied

Updated [pic_8259_tb.py:421](../../../dv/tbclasses/pic_8259/pic_8259_tb.py#L421):

```python
# Before: init_complete = (status >> 7) & 1
# After:  init_complete = status & 1  # init_complete is bit 0
```

### Verification

STATUS register correctly reads 0x09 = 0b00001001:
- bit 0: init_complete = 1 ✓
- bits 3-1: icw_step = 4 (INIT_COMPLETE state) ✓

---

## Summary

| Issue | Priority | Status | Tests Affected |
|-------|----------|--------|----------------|
| Missing INTA Cycle | High | Open | 3/6 failing |
| Auto-Reset Init | Medium | Fixed | 0 failing |
| Init_Complete Bit | Low | Fixed | 0 failing |

**Next Steps:**
1. Implement INTA auto-generation (Option 2)
2. Update pic_8259_core to use INTA signal
3. Verify all 6 tests pass

---

**Maintained By:** RTL Design Sherpa Project
