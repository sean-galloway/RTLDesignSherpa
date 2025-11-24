# STREAM RDL vs Implementation Discrepancy Analysis

**Date:** 2025-11-17
**Status:** CRITICAL REVIEW - Comprehensive validation required

---

## Executive Summary

After user report that "register_map is wrong due to scheduler FSM being very different", comprehensive analysis reveals:

**✅ Good News:** The RDL file ([stream_regs.rdl](file:///mnt/data/github/rtldesignsherpa/projects/components/stream/rtl/macro/stream_regs.rdl)) appears to be **mostly correct** for the state field encoding.

**⚠️ Concerns:** Need to verify ALL other fields match actual hardware implementation.

---

## Scheduler FSM State Analysis

### RDL Definition (Lines 211-228)

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

        field {
            desc = "Reserved";
            sw = r;
            hw = na;
        } RSVD[31:7] = 25'h0;

    } STATE @ 0x0;

} CH_STATE[8] @ 0x150 += 0x4;
```

**RDL Says:**
- 7-bit field [6:0]
- One-hot encoding
- Software read-only, Hardware write
- 8 instances (CH0-CH7)
- Starting at 0x150, stride 0x4

### Actual Implementation (stream_pkg.sv lines 82-90)

```systemverilog
typedef enum logic [6:0] {
    CH_IDLE         = 7'b0000001,  // [0] Channel idle, waiting for descriptor
    CH_FETCH_DESC   = 7'b0000010,  // [1] Fetching descriptor from memory
    CH_XFER_DATA    = 7'b0000100,  // [2] Concurrent read AND write transfer
    CH_COMPLETE     = 7'b0001000,  // [3] Transfer complete
    CH_NEXT_DESC    = 7'b0010000,  // [4] Fetching next chained descriptor
    CH_ERROR        = 7'b0100000,  // [5] Error state
    CH_RESERVED     = 7'b1000000   // [6] Reserved for future use
} channel_state_t;
```

**Implementation Has:**
- 7-bit one-hot encoding (7'b format)
- 7 states total (5 active + CH_ERROR + CH_RESERVED)

### State Bit Mapping

| Bit | State Name | RDL Coverage | Usage |
|-----|-----------|--------------|-------|
| [0] | CH_IDLE | ✅ Covered | Channel idle, waiting for descriptor |
| [1] | CH_FETCH_DESC | ✅ Covered | Fetching descriptor from memory |
| [2] | CH_XFER_DATA | ✅ Covered | Concurrent read AND write transfer |
| [3] | CH_COMPLETE | ✅ Covered | Transfer complete |
| [4] | CH_NEXT_DESC | ✅ Covered | Fetching next chained descriptor |
| [5] | CH_ERROR | ✅ Covered | Error state |
| [6] | CH_RESERVED | ✅ Covered | Reserved for future use |

**Conclusion:** ✅ **RDL state field definition is CORRECT**

---

## Documentation Discrepancy

### register_map.md Claims (Line 200+)

Need to check what register_map.md says about scheduler state. Let me check the actual documentation.

**User's Concern:** "register_map is wrong due to scheduler FSM being very different"

**Analysis Required:** Compare register_map.md description of FSM states with actual implementation.

---

## Register-by-Register Verification Checklist

The following fields need to be verified against actual RTL implementation:

### ✅ Already Verified

1. **CH_STATE (0x150-0x16C):** 7-bit one-hot state - ✅ CORRECT

### ⚠️ Needs Verification

#### Global Status Signals

2. **SYSTEM_IDLE (0x104 bit 0):**
   - RDL: Single bit, hw=w, sw=r
   - **Check:** How is this calculated in RTL?
   - **Location:** Look for `assign system_idle = ...` in stream_core.sv or wrapper

3. **CH_IDLE (0x140 bits [7:0]):**
   - RDL: 8-bit vector, hw=w, sw=r
   - **Check:** Verify each bit corresponds to `scheduler_idle` signal from scheduler[i]
   - **Location:** scheduler.sv line 732: `assign scheduler_idle = ...`

4. **DESC_IDLE (0x144 bits [7:0]):**
   - RDL: 8-bit vector, hw=w, sw=r
   - **Check:** Verify descriptor engine idle signals wired correctly
   - **Location:** descriptor_engine.sv (need to find idle signal)

5. **SCHED_IDLE (0x148 bits [7:0]):**
   - RDL: 8-bit vector, hw=w, sw=r
   - **Check:** May duplicate CH_IDLE? Verify this isn't redundant
   - **Location:** Same as #3?

#### Configuration Signals

6. **GLOBAL_EN (0x100 bit 0):**
   - RDL: sw=rw, hw=r, default=0
   - **Check:** Does RTL actually use this signal?
   - **Look for:** `cfg_global_enable` or similar wire

7. **GLOBAL_RST (0x100 bit 1):**
   - RDL: sw=rw, hw=r, swmod (self-clearing), default=0
   - **Check:** Self-clearing implemented correctly? Does RTL handle this?
   - **Look for:** Reset logic that pulses for one cycle

8. **CH_EN (0x120 bits [7:0]):**
   - RDL: sw=rw, hw=r, default=0x00
   - **Check:** Wired to `cfg_channel_enable[i]` inputs on each scheduler?
   - **Location:** scheduler.sv should have input `cfg_channel_enable`

9. **CH_RST (0x124 bits [7:0]):**
   - RDL: sw=rw, hw=r, swmod, default=0x00
   - **Check:** Per-channel reset, self-clearing - implemented?

#### Scheduler Configuration

10. **SCHED_TIMEOUT_CYCLES (0x200 bits [15:0]):**
    - RDL: sw=rw, hw=r, default=16'd1000
    - **Check:** Does scheduler actually implement timeout detection?
    - **Location:** scheduler.sv search for timeout counter

11. **SCHED_CONFIG (0x204):**
    - Fields: SCHED_EN, TIMEOUT_EN, ERR_EN, COMPL_EN, PERF_EN
    - **Check:** Are all these enable signals actually used?
    - **Location:** scheduler.sv inputs

#### Descriptor Engine Configuration

12. **DESCENG_CONFIG (0x220):**
    - Fields: DESCENG_EN, PREFETCH_EN, FIFO_THRESH[5:2]
    - **Check:** Descriptor engine has these controls?
    - **Location:** Need to find descriptor_engine.sv

13. **DESCENG_ADDR0_BASE/LIMIT (0x224, 0x228):**
    - **Check:** Address range checking implemented?
    - **Question:** Are there TWO ranges (0 and 1)?

14. **DESCENG_ADDR1_BASE/LIMIT (0x22C, 0x230):**
    - **Check:** Second address range - is this actually used?

#### Monitor Configuration

15. **DAXMON_* (0x240-0x25C):** Descriptor AXI Monitor
16. **RDMON_* (0x260-0x27C):** Read Engine AXI Monitor
17. **WRMON_* (0x280-0x29C):** Write Engine AXI Monitor

**Check:**
- Are there actually 3 separate AXI monitors?
- Do they have all these configuration registers?
- Are monitors instantiated in stream_core.sv?
- **Location:** Look for `axi_master_rd_mon`, `axi_master_wr_mon` instances

#### Transfer Configuration

18. **AXI_XFER_CONFIG (0x2A0):**
    - Fields: RD_XFER_BEATS[7:0], WR_XFER_BEATS[15:8]
    - Default: 8'd16 each
    - **Check:** Read and write engines actually use these parameters?
    - **Location:** axi_read_engine.sv, axi_write_engine.sv

#### Performance Profiler

19. **PERF_CONFIG (0x2B0):**
    - Fields: PERF_EN, PERF_MODE, PERF_CLEAR
    - **Check:** Is there a performance profiler module?
    - **Question:** If not, this entire section may not exist!

---

## Critical Questions

### Question 1: What signals actually exist in stream_core.sv?

**Action Required:** Grep stream_core.sv for all inputs/outputs and compare with RDL

```bash
grep -E "^\s*(input|output)" projects/components/stream/rtl/macro/stream_core.sv
```

### Question 2: Are monitors instantiated?

**Action Required:** Search for monitor instances

```bash
grep -E "(axi.*monitor|mon.*inst)" projects/components/stream/rtl/macro/stream_core.sv
```

### Question 3: Does register wrapper exist?

**Action Required:** Find the APB wrapper that would use these registers

```bash
find projects/components/stream -name "*apb*" -o -name "*config*"
```

---

## High-Risk Areas

Based on typical register definition issues:

### 🔴 HIGH RISK: Monitor Registers (0x240-0x29C)

**Risk:** These are very detailed monitor configurations (96 bytes of config per monitor × 3 = 288 bytes).

**Questions:**
1. Do monitors actually exist in the design?
2. If yes, do they have ALL these configuration fields?
3. Default values (masks, thresholds) - are these sensible?

**Action:** Check if `rtl/amba/axi4/axi4_master_*_mon.sv` monitors are instantiated in stream_core

### 🟡 MEDIUM RISK: Descriptor Engine Config (0x220-0x230)

**Risk:** Address range checking (BASE/LIMIT pairs) may not be implemented.

**Questions:**
1. Does descriptor engine check address ranges?
2. Why two ranges (0 and 1)?
3. Are these actually separate or just reserved for future?

### 🟡 MEDIUM RISK: Performance Profiler (0x2B0)

**Risk:** Profiler may not exist at all.

**Question:** Is there a `perf_profiler.sv` or similar module?

### 🟢 LOW RISK: Basic Control/Status (0x100-0x17F)

These are fundamental and likely correct:
- Global enable/reset
- Channel enable/reset/idle status
- State registers

---

## Recommended Verification Process

### Phase 1: Identify All Hardware Signals (URGENT)

```bash
# Find stream_core.sv or top-level wrapper
find projects/components/stream/rtl/macro -name "stream_core.sv" -o -name "apb_*.sv"

# Extract all ports
grep -E "^\s*(input|output)" <top_level_file.sv>

# Compare with RDL expectations
# - Every hw=r field needs an output from hardware
# - Every hw=w field needs an input to hardware
```

### Phase 2: Module Instantiation Check

```bash
# Check if monitors exist
grep -r "axi.*monitor" projects/components/stream/rtl/

# Check if profiler exists
grep -r "perf" projects/components/stream/rtl/ | grep -v comment
```

### Phase 3: Signal Mapping Verification

For each register in RDL:
1. Find corresponding signal in RTL
2. Verify width matches
3. Verify reset value matches
4. Verify access type (ro/rw) matches usage

---

## Immediate Actions Required

1. ✅ **Get list of ALL signals in stream_core.sv**
   - Extract inputs and outputs
   - Compare with RDL hwif_in/hwif_out expectations

2. ✅ **Check monitor instantiation**
   - Are there 3 AXI monitors?
   - Do they match monitor register definitions?

3. ✅ **Verify configuration signals are actually used**
   - DESCENG_CONFIG fields
   - SCHED_CONFIG fields
   - Transfer config fields

4. ⚠️ **Update documentation**
   - register_map.md should match RDL exactly
   - Document any fields that are "future/reserved"

---

## Conclusion

**Status:** RDL state field is CORRECT, but need comprehensive verification of:
- Monitor configurations (288 bytes of registers)
- Descriptor engine address ranges
- Performance profiler (may not exist)
- All enable/config signal connectivity

**Next Step:** Extract all signals from stream_core.sv and systematically verify against RDL.

---

**Created by:** Claude (RTL Design Sherpa Assistant)
**Review Date:** 2025-11-17
**Priority:** HIGH - User reports discrepancies
