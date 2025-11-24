# STREAM Register Definition (PeakRDL) Review

**File:** [stream_regs.rdl](file:///mnt/data/github/rtldesignsherpa/projects/components/stream/rtl/macro/stream_regs.rdl)
**Date:** 2025-11-17
**Status:** Comprehensive technical review

---

## Executive Summary

✅ **Overall Assessment: PASS with minor recommendations**

The stream_regs.rdl file is **well-structured and correctly defined**. The register definitions are consistent with the [register_map.md](file:///mnt/data/github/rtldesignsherpa/projects/components/stream/docs/stream_spec/ch04_registers/register_map.md) specification. A few minor issues were identified for improvement.

---

## Detailed Review

### 1. Structure and Organization ✅

**Rating:** GOOD

- Clear logical grouping by function
- Appropriate use of comments for section headers
- Good naming conventions
- Address map starts at 0x100 (correct - 0x000-0x03F reserved for kick-off)

**Verification:**
- Line 22-29: Proper addrmap declaration with descriptive metadata
- Lines 30-32: Correct defaults (regwidth=32, accesswidth=32, alignment=4)

---

### 2. Address Allocation ✅

**Rating:** GOOD

**Address Map:**
| Range | Purpose | Status |
|-------|---------|--------|
| 0x100 - 0x11F | Global Control/Status | ✅ Correct |
| 0x120 - 0x17F | Per-Channel Control/Status | ✅ Correct |
| 0x200 - 0x21F | Scheduler Configuration | ✅ Correct |
| 0x220 - 0x23F | Descriptor Engine Config | ✅ Correct |
| 0x240 - 0x25F | Descriptor AXI Monitor | ✅ Correct |
| 0x260 - 0x27F | Read Engine AXI Monitor | ✅ Correct |
| 0x280 - 0x29F | Write Engine AXI Monitor | ✅ Correct |
| 0x2A0 - 0x2AF | AXI Transfer Config | ✅ Correct |
| 0x2B0 - 0x2BF | Performance Profiler | ✅ Correct |

**No address conflicts detected.**

**Alignment:**
- All registers at 4-byte boundaries ✅
- Register array at line 229: `CH_STATE[8] @ 0x150 += 0x4` ✅ Correct stride

---

### 3. Field Bit Assignments ⚠️

**Rating:** MOSTLY GOOD with one issue

**Issue #1: FIFO_THRESH field range (Line 319)**
```systemverilog
field {
    desc = "FIFO threshold [5:2] - prefetch threshold (4 bits)";
    sw = rw;
    hw = r;
} FIFO_THRESH[5:2] = 4'h8;
```

**Problem:** Field is declared as bits [5:2], which is 4 bits, but should be [5:0] to use all available bits, or the description should say "bits [5:2] of register" more clearly.

**Recommendation:** Clarify intent. If this is meant to pack into bits [5:2] of the 32-bit register (with bits [1:0] and [31:6] as other fields or reserved), that's fine. But currently lines 308-326 show:
- Bit 0: DESCENG_EN
- Bit 1: PREFETCH_EN
- Bits [5:2]: FIFO_THRESH
- Bits [31:6]: RSVD

This is **CORRECT** but unusual. Most designs would use [3:0] for a 4-bit threshold and place it at the bottom of the register.

**Impact:** LOW - Works as designed, just unconventional.

---

### 4. Access Permissions ✅

**Rating:** GOOD

All access modes are correctly specified:

**Global Control (0x100):**
- GLOBAL_EN: sw=rw, hw=r ✅ (Software writes, hardware reads)
- GLOBAL_RST: sw=rw, hw=r, swmod ✅ (Self-clearing)
- RSVD: sw=r, hw=na ✅ (Read-only zeros)

**Global Status (0x104):**
- SYSTEM_IDLE: sw=r, hw=w ✅ (Software reads, hardware writes)

**Version (0x108):**
- All fields: sw=r, hw=na ✅ (Read-only constants)

**Pattern is consistent across all 38 registers.**

---

### 5. Reserved Field Handling ✅

**Rating:** GOOD

All registers properly include reserved fields for unused bits:

```systemverilog
field {
    desc = "Reserved";
    sw = r;
    hw = na;
} RSVD[31:X] = ...;
```

**Verified:**
- Line 52-55: GLOBAL_CTRL reserved [31:2] ✅
- Line 70-73: GLOBAL_STATUS reserved [31:1] ✅
- Line 100-103: VERSION reserved [31:24] ✅
- Pattern repeated consistently throughout

---

### 6. Self-Clearing Fields ✅

**Rating:** GOOD

Two registers correctly use `swmod` for self-clearing behavior:

1. **GLOBAL_RST (Line 48-49):**
   ```systemverilog
   field {
       desc = "Global reset - resets all channels and state machines";
       sw = rw;
       hw = r;
       swmod;  // Self-clearing
   } GLOBAL_RST = 1'b0;
   ```

2. **CH_RST (Line 137):**
   ```systemverilog
   field {
       desc = "Channel reset bits [7:0] - write 1 to reset channel";
       sw = rw;
       hw = r;
       swmod;  // Self-clearing
   } CH_RST[7:0] = 8'h00;
   ```

3. **PERF_CLEAR (Line 999):**
   ```systemverilog
   field {
       desc = "Performance profiler clear - write 1 to clear counters";
       sw = rw;
       hw = r;
       swmod;  // Self-clearing
   } PERF_CLEAR = 1'b0;
   ```

**All correctly marked.** ✅

---

### 7. Default Values ✅

**Rating:** GOOD

All default values are sensible and safe:

**Key defaults verified:**
- GLOBAL_EN = 0 (disabled at reset) ✅
- GLOBAL_RST = 0 (no reset asserted) ✅
- CH_EN = 0x00 (all channels disabled) ✅
- Timeouts = 10000 cycles (reasonable) ✅
- Latency thresholds = 5000 cycles (reasonable) ✅
- Transfer beats = 16 (max burst) ✅
- All enable bits default to appropriate values ✅

---

### 8. Monitor Configuration Consistency ⚠️

**Rating:** GOOD with recommendation

Three AXI monitors (Descriptor, Read, Write) have **identical** register structures:

| Offset | Descriptor (0x240) | Read (0x260) | Write (0x280) | Field Name |
|--------|-------------------|--------------|---------------|------------|
| +0x00  | DAXMON_ENABLE     | RDMON_ENABLE | WRMON_ENABLE  | MON_EN, ERR_EN, COMPL_EN, TIMEOUT_EN, PERF_EN |
| +0x04  | DAXMON_TIMEOUT    | RDMON_TIMEOUT | WRMON_TIMEOUT | TIMEOUT_CYCLES[31:0] |
| +0x08  | DAXMON_LATENCY_THRESH | RDMON_LATENCY_THRESH | WRMON_LATENCY_THRESH | LATENCY_THRESH[31:0] |
| +0x0C  | DAXMON_PKT_MASK   | RDMON_PKT_MASK | WRMON_PKT_MASK | PKT_MASK[15:0] |
| +0x10  | DAXMON_ERR_CFG    | RDMON_ERR_CFG | WRMON_ERR_CFG | ERR_SELECT[3:0], ERR_MASK[15:8] |
| +0x14  | DAXMON_MASK1      | RDMON_MASK1  | WRMON_MASK1   | TIMEOUT_MASK, COMPL_MASK |
| +0x18  | DAXMON_MASK2      | RDMON_MASK2  | WRMON_MASK2   | THRESH_MASK, PERF_MASK |
| +0x1C  | DAXMON_MASK3      | RDMON_MASK3  | WRMON_MASK3   | ADDR_MASK, DEBUG_MASK |

**Consistency check:** All three blocks have identical structure ✅

**Recommendation:** Consider using a PeakRDL `regfile` to define the pattern once and instantiate three times:

```systemverilog
// Define reusable monitor register block
regfile axi_monitor_regs {
    name = "AXI Monitor Configuration";

    reg {
        name = "Monitor Enable";
        field { ... } MON_EN = 1'b1;
        field { ... } ERR_EN = 1'b1;
        // ... all common fields
    } ENABLE @ 0x0;

    reg { ... } TIMEOUT @ 0x4;
    reg { ... } LATENCY_THRESH @ 0x8;
    // ... etc
};

// Instantiate three times with prefixes
axi_monitor_regs DAXMON @ 0x240;
axi_monitor_regs RDMON  @ 0x260;
axi_monitor_regs WRMON  @ 0x280;
```

**Impact:** LOW - Current approach works, but DRY principle would improve maintainability.

---

### 9. Version Field ⚠️

**Rating:** MINOR ISSUE

**Line 91:** `MAJOR[15:8] = 8'h02;  // v2`

The documentation at [register_map.md:135](file:///mnt/data/github/rtldesignsherpa/projects/components/stream/docs/stream_spec/ch04_registers/register_map.md#L135) says:

```
| 15:8   | MAJOR         | RO   | 0x01  | Major version (1)                  |
```

**Mismatch:** RDL says v2, documentation says v1.

**Recommendation:** Update documentation to match v2, or clarify versioning scheme.

**Impact:** LOW - Informational only, doesn't affect functionality.

---

### 10. Field Naming Consistency ⚠️

**Rating:** MINOR ISSUE

**ERR_CFG register has split reserved fields (Lines 476-491):**

```systemverilog
field {
    desc = "Error select [3:0] - error type selection";
    sw = rw;
    hw = r;
} ERR_SELECT[3:0] = 4'h0;

field {
    desc = "Reserved";
    sw = r;
    hw = na;
} RSVD1[7:4] = 4'h0;  // ← Named RSVD1

field {
    desc = "Error mask [15:8] - error type filtering";
    sw = rw;
    hw = r;
} ERR_MASK[15:8] = 8'hFF;

field {
    desc = "Reserved";
    sw = r;
    hw = na;
} RSVD2[31:16] = 16'h0;  // ← Named RSVD2
```

**Issue:** Using numbered RSVD fields (RSVD1, RSVD2) is necessary when there are multiple reserved regions in one register, but inconsistent with other registers that just use RSVD.

**Impact:** NONE - PeakRDL handles this correctly. Just a style observation.

---

### 11. Channel State Register Array ✅

**Rating:** GOOD

**Lines 207-229:** Per-channel state register file correctly defined:

```systemverilog
regfile {
    name = "Per-Channel State Registers";
    desc = "Detailed state for individual channel";

    reg {
        name = "Channel State";
        desc = "Current FSM state of scheduler (one-hot 7-bit encoding)";

        field {
            desc = "Scheduler state [6:0] - one-hot encoding";
            sw = r;
            hw = w;
        } STATE[6:0];

        // ... reserved field

    } STATE @ 0x0;

} CH_STATE[8] @ 0x150 += 0x4;
```

**Array allocation:**
- 8 channels ✅
- Starting at 0x150 ✅
- Stride of 0x4 bytes (one 32-bit register per channel) ✅
- Matches documentation ✅

**Addresses generated:**
- CH0_STATE: 0x150
- CH1_STATE: 0x154
- CH2_STATE: 0x158
- ...
- CH7_STATE: 0x16C

All within 0x120-0x17F range ✅

---

### 12. Mask Registers Bit Allocation ⚠️

**Rating:** DESIGN QUESTION

**DAXMON_MASK1, RDMON_MASK1, WRMON_MASK1 (Lines 495-517):**

```systemverilog
field {
    desc = "Timeout mask [7:0]";
    sw = rw;
    hw = r;
} TIMEOUT_MASK[7:0] = 8'hFF;

field {
    desc = "Completion mask [15:8]";
    sw = rw;
    hw = r;
} COMPL_MASK[15:8] = 8'h00;

field {
    desc = "Reserved";
    sw = r;
    hw = na;
} RSVD[31:16] = 16'h0;
```

**Question:** Why are masks 8-bit instead of 16-bit (to match PKT_MASK)?

**Observation:** PKT_MASK is 16-bit (line 455), but individual category masks (TIMEOUT_MASK, COMPL_MASK, etc.) are 8-bit.

**Recommendation:** Document the mask bit allocation scheme. Is each mask independent, or do they map to specific packet types?

**Impact:** LOW - Likely intentional design, just needs clarification in comments.

---

## Summary of Issues

| Issue | Severity | Line(s) | Description | Recommendation |
|-------|----------|---------|-------------|----------------|
| 1 | LOW | 319 | FIFO_THRESH at bits [5:2] | Add comment explaining bit packing |
| 2 | LOW | 91 | Version mismatch (v2 vs v1) | Update documentation to v2 |
| 3 | INFO | 240-945 | Monitor configs repeated 3× | Consider regfile reuse (optional) |
| 4 | INFO | 476-491 | Split reserved fields need RSVD1/RSVD2 names | Acceptable, just document pattern |
| 5 | INFO | 495-541 | 8-bit masks vs 16-bit PKT_MASK | Document mask bit allocation |

---

## Recommendations for PeakRDL Generation

When generating RTL from this RDL file:

1. **Verify generated package matches specification:**
   ```bash
   cd projects/components/stream/rtl/macro
   peakrdl systemverilog stream_regs.rdl -o generated/
   ```

2. **Check generated register file:**
   - Confirm all 38 registers present
   - Verify address offsets match RDL
   - Check self-clearing logic for GLOBAL_RST, CH_RST, PERF_CLEAR

3. **Integration checklist:**
   - [ ] Connect APB interface signals
   - [ ] Wire hwif_in status signals from hardware
   - [ ] Wire hwif_out control signals to hardware
   - [ ] Handle kick-off registers separately (apbtodescr.sv)
   - [ ] Test self-clearing behavior in simulation
   - [ ] Verify reset values in testbench

4. **Documentation sync:**
   - [ ] Update register_map.md with v2 version number
   - [ ] Generate HTML docs from RDL
   - [ ] Update PRD with final register count and addresses

---

## Conclusion

✅ **The stream_regs.rdl file is well-designed and production-ready.**

**Strengths:**
- Comprehensive coverage of all configuration needs
- Consistent structure and naming
- Correct PeakRDL syntax
- Good default values
- Proper access mode specifications

**Minor improvements:**
- Add clarifying comments for bit packing (FIFO_THRESH)
- Sync version numbers with documentation
- Consider regfile reuse for monitor configs (maintainability)

**No blocking issues found. Ready for PeakRDL code generation.**

---

**Reviewed by:** Claude (RTL Design Sherpa Assistant)
**Review Date:** 2025-11-17
**Next Steps:** Generate SystemVerilog from RDL and integrate with stream_core.sv
