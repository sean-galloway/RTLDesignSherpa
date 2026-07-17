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

# register_map.md Documentation Audit

**Date:** 2025-11-22
**Status:** 🔴 **CRITICAL ERRORS FOUND - Corrections in progress**

---

## Executive Summary

Comprehensive audit of [register_map.md](register_map.md) against the RDL source file ([stream_regs.rdl](../../../rtl/macro/stream_regs.rdl)) found **CRITICAL ERRORS** that would cause software failures.

**Errors Found:**
1. ✅ **FIXED:** Scheduler state encoding (4-bit binary vs 7-bit one-hot)
2. ✅ **FIXED:** VERSION register values (MAJOR/MINOR)
3. ❌ **TODO:** Monitor register addresses (21 registers missing)
4. ✅ **FIXED:** Code examples using wrong state encodings

---

## Error 1: Scheduler State Encoding (CRITICAL) - ✅ FIXED

### Problem

**Documentation showed (WRONG):**
```
| 0x150  | CH0_STATE  | 3:0   | STATE    | RO   | Channel 0 scheduler state      |

: Problem

State Encoding:
0x0 = CH_IDLE       - Idle, waiting for descriptor
0x1 = CH_FETCH_DESC - Fetching descriptor
0x2 = CH_READ_DATA  - Reading source data       ← WRONG NAME
0x3 = CH_WRITE_DATA - Writing destination data  ← WRONG NAME
0x4 = CH_COMPLETE   - Transfer complete
0x5 = CH_NEXT_DESC  - Chaining to next descriptor
0x6 = CH_ERROR      - Error state
```

**Multiple Errors:**
- ❌ Field width: **[3:0]** (4 bits) - WRONG, should be [6:0] (7 bits)
- ❌ Encoding: **Binary** (0x0, 0x1, etc.) - WRONG, should be one-hot
- ❌ State names: CH_READ_DATA, CH_WRITE_DATA - **DON'T EXIST IN RTL**
- ❌ Missing state: CH_RESERVED (bit 6)

### Correct Implementation

**RDL ([stream_regs.rdl:211](../../../rtl/macro/stream_regs.rdl#L211)):**
```systemverilog
field {
    desc = "Scheduler state [6:0] - one-hot encoding";
    sw = r;
    hw = w;
} STATE[6:0];
```

**RTL ([stream_pkg.sv:82-90](../../../rtl/includes/stream_pkg.sv#L82)):**
```systemverilog
typedef enum logic [6:0] {
    CH_IDLE         = 7'b0000001,  // [0] Bit 0 = 0x01
    CH_FETCH_DESC   = 7'b0000010,  // [1] Bit 1 = 0x02
    CH_XFER_DATA    = 7'b0000100,  // [2] Bit 2 = 0x04  ← CORRECT NAME
    CH_COMPLETE     = 7'b0001000,  // [3] Bit 3 = 0x08
    CH_NEXT_DESC    = 7'b0010000,  // [4] Bit 4 = 0x10
    CH_ERROR        = 7'b0100000,  // [5] Bit 5 = 0x20
    CH_RESERVED     = 7'b1000000   // [6] Bit 6 = 0x40
} channel_state_t;
```

**Impact:**
- 🔴 Software polling for state==0x0 would fail (actual value is 0x01)
- 🔴 Wrong bit masks (0xF vs 0x7F) would truncate state bits
- 🔴 Wrong state names would confuse developers

**Status:** ✅ Fixed (2025-11-22)

---

## Error 2: VERSION Register Values - ✅ FIXED

### Problem

**Documentation showed:**
```
| 15:8   | MAJOR         | RO   | 0x01  | Major version (1)                  |
| 7:0    | MINOR         | RO   | 0x00  | Minor version (0)                  |

: Problem
```

**RDL actually has:**
```
| 15:8   | MAJOR         | RO   | 0x00  | Major version (0)                  |
| 7:0    | MINOR         | RO   | 0x5A  | Minor version (90 decimal = 0.90)  |

: Problem
```

**Impact:** Minor - software version checking would see wrong version

**Status:** ✅ Fixed (2025-11-22) - Both RDL and register_map.md corrected

---

## Error 3: Monitor Register Addresses (CRITICAL) - ❌ TODO

### Problem

**Documentation shows:**
```
#### DAXMON_CONFIG (0x240)
... (single CONFIG register)

#### RDMON_CONFIG (0x244)  ← WRONG ADDRESS!
... (single CONFIG register)
```

**Problems:**
- Shows only 1 register per monitor (CONFIG)
- RDMON_CONFIG at 0x244 - **WRONG** (that address is actually DAXMON_TIMEOUT)
- Missing 7 other registers per monitor
- Documentation claims monitors end at 0x27F, but RDL goes to 0x29C

### Actual RDL Structure

Each monitor has **8 registers** (stride 0x20):

**DAXMON (Descriptor AXI): 0x240 - 0x25C**
```
0x240: DAXMON_ENABLE         - Enable/config (MON_EN, ERR_EN, PERF_EN, etc.)
0x244: DAXMON_TIMEOUT        - Timeout cycles (32-bit)
0x248: DAXMON_LATENCY_THRESH - Latency threshold (32-bit)
0x24C: DAXMON_PKT_MASK       - Packet type mask (16-bit)
0x250: DAXMON_ERR_CFG        - Error config (ERR_SELECT + ERR_MASK)
0x254: DAXMON_MASK1          - Timeout/Completion masks
0x258: DAXMON_MASK2          - Threshold/Performance masks
0x25C: DAXMON_MASK3          - Address/Debug masks
```

**RDMON (Read Data AXI): 0x260 - 0x27C** (same structure)

**WRMON (Write Data AXI): 0x280 - 0x29C** (same structure)

**Impact:**
- 🔴 **CRITICAL** - Software cannot configure monitors
- 🔴 Accessing 0x244 for "RDMON_CONFIG" actually writes DAXMON_TIMEOUT
- 🔴 **21 registers completely undocumented** (7 per monitor × 3)

**Status:** ❌ **NOT FIXED** - Requires complete rewrite of monitor section (~200 lines)

---

## Error 4: Code Examples Using Wrong Encoding - ✅ FIXED

### Example 1: Polling for Idle State

**Was (WRONG):**
```c
while ((read32(BASE + CH0_STATE) & 0xF) != 0x0) {  // ← WRONG
    // Wait for CH_IDLE state (0x0)
}
```

**Fixed (CORRECT):**
```c
while ((read32(BASE + CH0_STATE) & 0x7F) != 0x01) {
    // Wait for CH_IDLE state (bit 0 = 0x01)
}
```

### Example 2: Error Detection

**Was (WRONG):**
```c
uint32_t state = read32(BASE + CH0_STATE + (ch * 4)) & 0xF;
if (state == 0x6) {  // CH_ERROR  ← WRONG
```

**Fixed (CORRECT):**
```c
uint32_t state = read32(BASE + CH0_STATE + (ch * 4)) & 0x7F;
if (state & 0x20) {  // CH_ERROR (bit 5)
```

**Status:** ✅ Fixed (2025-11-22)

---

## Summary

| Error | Severity | Status | Impact |
|-------|----------|--------|--------|
| Scheduler state encoding | 🔴 CRITICAL | ✅ FIXED | Software fails to detect states |
| VERSION register values | ⚠️ MINOR | ✅ FIXED | Version mismatch |
| Monitor addresses (21 missing regs) | 🔴 CRITICAL | ❌ TODO | Cannot configure monitors |
| Code example: Idle polling | 🔴 CRITICAL | ✅ FIXED | Software hangs |
| Code example: Error detection | 🔴 CRITICAL | ✅ FIXED | Errors not detected |

: Summary

**Progress:** 4 of 5 errors fixed (80% complete)

---

## Remaining Work

### Monitor Section Rewrite

The monitor configuration section needs **complete replacement** with:

1. All 8 registers per monitor documented:
   - ENABLE (MON_EN, ERR_EN, PERF_EN, TIMEOUT_EN, COMPL_EN bits)
   - TIMEOUT (32-bit timeout cycles)
   - LATENCY_THRESH (32-bit latency threshold)
   - PKT_MASK (16-bit packet type mask)
   - ERR_CFG (ERR_SELECT[3:0] + ERR_MASK[7:0])
   - MASK1 (TIMEOUT_MASK + COMPL_MASK)
   - MASK2 (THRESH_MASK + PERF_MASK)
   - MASK3 (ADDR_MASK + DEBUG_MASK)

2. Correct addresses:
   - DAXMON: 0x240-0x25C
   - RDMON: 0x260-0x27C
   - WRMON: 0x280-0x29C

3. Bit field descriptions for each register

4. Code examples showing monitor configuration

**Estimated Size:** ~200 lines of documentation

---

## Root Cause

**Why did these errors occur?**

1. **Manual documentation maintenance**
   - Documentation not auto-generated from RDL
   - Copy-paste errors and incomplete updates
   - No automated validation

2. **Architecture changes not propagated**
   - Scheduler FSM changed from binary to one-hot encoding
   - State names changed (READ_DATA/WRITE_DATA → XFER_DATA)
   - Documentation not updated to reflect changes

3. **Incomplete register coverage**
   - Only subset of registers documented
   - Monitor registers severely incomplete (1 of 8 per monitor)

---

## Prevention

**Recommendations to prevent future errors:**

1. **Auto-generate documentation from RDL**
   - Use `peakrdl-html` or `peakrdl-markdown` tools
   - Keep markdown as supplementary (examples, usage notes)
   - Mark auto-generated sections clearly

2. **Add validation**
   - Pre-commit hook to check RDL changes
   - Script to extract register tables from both RDL and markdown
   - Automated comparison to detect mismatches

3. **Code review process**
   - Any RDL change requires documentation review
   - Test code examples from documentation
   - Validate addresses, widths, reset values

---

## Validation Checklist

- [x] Scheduler state encoding (bits, values, names)
- [x] VERSION register (MAJOR, MINOR values)
- [x] Code example: Idle state polling
- [x] Code example: Error detection
- [ ] Monitor register addresses (DAXMON, RDMON, WRMON)
- [ ] Monitor register bit fields (all 8 regs × 3 monitors)
- [ ] Monitor code examples
- [ ] Verify all other register addresses match RDL
- [ ] Verify all field widths match RDL
- [ ] Verify all reset values match RDL
- [ ] Verify all access types (RO/RW) match RDL

**Progress:** 4 of 11 items complete (36%)

---

**Audit Performed By:** Claude (RTL Design Sherpa Assistant)
**Audit Date:** 2025-11-22
**Files Analyzed:**
- [register_map.md](register_map.md) (467 lines)
- [stream_regs.rdl](../../../rtl/macro/stream_regs.rdl) (1010 lines)
- [stream_pkg.sv](../../../rtl/includes/stream_pkg.sv) (state encoding)

**Recommendation:** Complete monitor section rewrite before software development begins.
