# AXI4 Data Width Converter - Code Sharing Analysis

**Date:** 2025-10-24
**Purpose:** Analyze potential code sharing between read and write converters
**Question:** Can common logic be extracted and parameterized for both converters?

---

## Executive Summary

**Short Answer:** **Limited sharing potential - NOT RECOMMENDED**

**Key Findings:**
1. **Address Conversion:** 95% identical - could be shared, but low value (only ~20 lines each)
2. **Data Conversion:** Structurally similar but operationally opposite - sharing would obscure logic
3. **Best Practice:** Keep separate for clarity and maintainability

**Recommendation:** Keep current architecture (separate read/write converters)

---

## Detailed Analysis

### 1. Address Channel Conversion (AW vs AR)

#### Similarity: 95% Identical

**Write Address (AW) Conversion:**
```systemverilog
// DOWNSIZE: Multiply burst length by ratio
assign m_axi_awlen = ((int_awlen + 8'd1) * 8'(WIDTH_RATIO)) - 8'd1;
assign m_axi_awsize = MASTER_SIZE[2:0];
assign m_axi_awid = int_awid;
assign m_axi_awaddr = int_awaddr;  // (upsize aligns to master width)
assign m_axi_awburst = int_awburst;
// ... (lock, cache, prot, qos, region, user)

// UPSIZE: Divide burst length by ratio
assign m_axi_awlen = ((int_awlen + 8'(WIDTH_RATIO)) / 8'(WIDTH_RATIO)) - 8'd1;
assign aligned_awaddr = {int_awaddr[AXI_ADDR_WIDTH-1:ALIGN_BITS], {ALIGN_BITS{1'b0}}};
```

**Read Address (AR) Conversion:**
```systemverilog
// DOWNSIZE: Multiply burst length by ratio
assign m_axi_arlen = ((int_arlen + 8'd1) * 8'(WIDTH_RATIO)) - 8'd1;
assign m_axi_arsize = MASTER_SIZE[2:0];
assign m_axi_arid = int_arid;
assign m_axi_araddr = int_araddr;  // (upsize aligns to master width)
assign m_axi_arburst = int_arburst;
// ... (lock, cache, prot, qos, region, user)

// UPSIZE: Divide burst length by ratio
assign m_axi_arlen = ((int_arlen + 8'(WIDTH_RATIO)) / 8'(WIDTH_RATIO)) - 8'd1;
assign aligned_araddr = {int_araddr[AXI_ADDR_WIDTH-1:ALIGN_BITS], {ALIGN_BITS{1'b0}}};
```

**Differences:**
- Signal name prefix only: `aw*` vs `ar*`
- **EXACT same formula for burst length conversion**
- **EXACT same address alignment logic**

**Could This Be Shared?**
- **Technically:** Yes, via SystemVerilog function or macro
- **Practically:** Low value - only ~20 lines of code per converter
- **Cost:** Added complexity and indirection

**Example Shared Function:**
```systemverilog
function automatic [7:0] convert_burst_length(
    input [7:0] slave_len,
    input bit upsize_mode,
    input int ratio
);
    if (upsize_mode)
        return ((slave_len + 8'(ratio)) / 8'(ratio)) - 8'd1;  // Upsize
    else
        return ((slave_len + 8'd1) * 8'(ratio)) - 8'd1;       // Downsize
endfunction

function automatic [AXI_ADDR_WIDTH-1:0] align_address(
    input [AXI_ADDR_WIDTH-1:0] addr,
    input int align_bits
);
    return {addr[AXI_ADDR_WIDTH-1:align_bits], {align_bits{1'b0}}};
endfunction
```

**Verdict:** **NOT WORTH IT**
- Saves ~20 lines but adds indirection
- Formulas are simple and obvious in current form
- Inline code is more readable

---

### 2. Data Channel Conversion - The Critical Difference

#### Key Observation: Opposite Operations

**Write Path:**
- DOWNSIZE = **Split** wide→narrow (W channel OUT to master)
- UPSIZE = **Accumulate** narrow→wide (W channel OUT to master)

**Read Path:**
- DOWNSIZE = **Accumulate** narrow→wide (R channel IN from master)
- UPSIZE = **Split** wide→narrow (R channel IN from master)

**Why Opposite?**
```
Write: Slave (narrow) ──accumulate──> Master (wide)  [UPSIZE]
Write: Slave (wide)   ──split──────> Master (narrow) [DOWNSIZE]

Read:  Master (wide)  ──split──────> Slave (narrow)  [UPSIZE]
Read:  Master (narrow)──accumulate──> Slave (wide)   [DOWNSIZE]
```

The **data flow direction** inverts the operation:
- Write flows OUT (slave→master)
- Read flows IN (master→slave)

#### Structural Comparison

**ACCUMULATE Pattern (Narrow→Wide):**

Used by:
- Write UPSIZE (lines 387-450 in _wr.sv)
- Read DOWNSIZE (lines 289-354 in _rd.sv)

Common structure:
```systemverilog
logic [WIDE_DATA_WIDTH-1:0] r_accumulator;
logic [PTR_WIDTH-1:0]        r_ptr;
logic                        r_valid;

// Accept narrow beat
if (narrow_valid && narrow_ready) begin
    r_accumulator[r_ptr*NARROW_WIDTH +: NARROW_WIDTH] <= narrow_data;

    if (r_ptr == PTR_WIDTH'(WIDTH_RATIO-1) || narrow_last) begin
        r_valid <= 1'b1;
        r_ptr <= '0;
    end else begin
        r_ptr <= r_ptr + 1'b1;
    end
end

// Send wide beat
if (r_valid && wide_ready) begin
    r_valid <= 1'b0;
end
```

**Key Differences:**
1. **Write UPSIZE:** Has WSTRB accumulation
   ```systemverilog
   r_wstrb_buffer[r_write_beat_ptr*S_STRB_WIDTH +: S_STRB_WIDTH] <= int_wstrb;
   ```

2. **Read DOWNSIZE:** Has RRESP OR-ing (error propagation)
   ```systemverilog
   if (r_accum_ptr == '0)
       r_rresp_buffered <= m_axi_rresp;
   else
       r_rresp_buffered <= r_rresp_buffered | m_axi_rresp;
   ```

**SPLIT Pattern (Wide→Narrow):**

Used by:
- Write DOWNSIZE (lines 334-386 in _wr.sv)
- Read UPSIZE (lines 355-441 in _rd.sv)

Common structure:
```systemverilog
logic [WIDE_DATA_WIDTH-1:0] r_buffer;
logic [PTR_WIDTH-1:0]        r_beat_ptr;
logic                        r_buffered;

// Accept wide beat
if (wide_valid && wide_ready && !r_buffered) begin
    r_buffer <= wide_data;
    r_buffered <= 1'b1;
    r_beat_ptr <= '0;
end

// Send narrow beat
if (r_buffered && narrow_ready) begin
    if (r_beat_ptr == PTR_WIDTH'(WIDTH_RATIO-1) || is_last) begin
        r_buffered <= 1'b0;
        r_beat_ptr <= '0;
    end else begin
        r_beat_ptr <= r_beat_ptr + 1'b1;
    end
end

// Extract narrow beat from wide buffer
assign narrow_data = r_buffer[r_beat_ptr*NARROW_WIDTH +: NARROW_WIDTH];
```

**Key Differences:**
1. **Write DOWNSIZE:** Simpler - no burst tracking needed
   ```systemverilog
   logic [PTR_WIDTH:0] r_beat_index;  // Just a counter
   ```

2. **Read UPSIZE:** Complex burst tracking (lines 367-370, 386-422)
   ```systemverilog
   logic [7:0] r_slave_beat_count;
   logic [7:0] r_slave_total_beats;
   logic       r_burst_active;

   // Needs to track when to send RLAST based on original ARLEN
   ```

**Why Read Needs Burst Tracking:**
- Read response (R channel) must send RLAST on correct beat
- When splitting 1 wide beat → 4 narrow beats, RLAST only on beat #4
- Must count total beats across entire burst (from ARLEN)
- Write doesn't need this because WLAST comes from slave input

---

## Shared Code Extraction Feasibility

### Option 1: Parameterized Accumulator/Splitter Functions

**Concept:** Extract accumulate and split logic into reusable functions

**Problems:**
1. **WSTRB vs RRESP handling** - different logic
2. **Burst tracking** - read needs it, write doesn't
3. **Signal mapping** - input vs output directions differ
4. **State variables** - can't share registers across functions

**Verdict:** **NOT FEASIBLE** - state machines can't be easily parameterized

---

### Option 2: Shared Package with Helper Functions

**Concept:** Create `axi4_dwidth_converter_pkg.sv` with:
- Burst length calculation functions
- Address alignment functions
- Common parameter definitions

**Example:**
```systemverilog
package axi4_dwidth_converter_pkg;

    function automatic [7:0] calc_upsize_burst_len(
        input [7:0] slave_len,
        input int   ratio
    );
        return ((slave_len + 8'(ratio)) / 8'(ratio)) - 8'd1;
    endfunction

    function automatic [7:0] calc_downsize_burst_len(
        input [7:0] slave_len,
        input int   ratio
    );
        return ((slave_len + 8'd1) * 8'(ratio)) - 8'd1;
    endfunction

    function automatic [63:0] align_address(
        input [63:0] addr,
        input int    align_bits
    );
        return {addr[63:align_bits], {align_bits{1'b0}}};
    endfunction

endpackage
```

**Benefits:**
- Centralizes burst length formulas
- Ensures consistency
- Easy to test and verify

**Costs:**
- Adds indirection (less readable)
- Only saves ~10-15 lines per converter
- Obscures simple arithmetic

**Verdict:** **LOW VALUE** - formulas are already obvious and tested

---

### Option 3: Macro-Based Code Generation

**Concept:** Use SystemVerilog macros to generate repetitive code

**Example:**
```systemverilog
`define AXI_ADDR_CONVERT(PREFIX, UPSIZE, DOWNSIZE) \
    generate \
        if (DOWNSIZE) begin : gen_``PREFIX``_downsize \
            assign m_axi_``PREFIX``len = ((int_``PREFIX``len + 8'd1) * 8'(WIDTH_RATIO)) - 8'd1; \
            // ... more assignments \
        end else begin : gen_``PREFIX``_upsize \
            assign m_axi_``PREFIX``len = ((int_``PREFIX``len + 8'(WIDTH_RATIO)) / 8'(WIDTH_RATIO)) - 8'd1; \
            // ... more assignments \
        end \
    endgenerate

// Usage:
`AXI_ADDR_CONVERT(aw, UPSIZE, DOWNSIZE)
`AXI_ADDR_CONVERT(ar, UPSIZE, DOWNSIZE)
```

**Problems:**
- **VERY hard to read and debug**
- Macro expansion is opaque
- IDE syntax highlighting breaks
- Error messages become cryptic

**Verdict:** **STRONGLY DISCOURAGED** - maintainability nightmare

---

## Recommendation

### Keep Current Architecture - Here's Why:

#### 1. **Clarity Over Clever**
Current code is:
- Easy to read and understand
- Self-documenting (each converter standalone)
- Easy to debug (no indirection)
- Easy to modify (no shared dependencies)

#### 2. **Minimal Duplication**
- Address conversion: ~20 lines (trivial arithmetic)
- Data conversion: Different enough that sharing obscures intent
- Total "duplicate" code: <50 lines per converter

#### 3. **Maintenance Benefits**
Separate converters mean:
- No risk of breaking write converter when fixing read converter
- No complex parameterization to understand
- No shared state to coordinate
- Each file is completely standalone

#### 4. **Performance Considerations**
- No function call overhead
- No macro expansion complexity
- Direct, inline logic for synthesis optimization

#### 5. **The "Rule of Three"**
Software engineering principle: Don't abstract until you have ≥3 instances of duplication.

We have TWO converters. If we add a third (e.g., AXI-Stream width converter), THEN consider abstraction.

---

## What About the Burst Length Formula?

### Current Duplication

The burst length calculation appears 4 times:
1. Write UPSIZE: `((int_awlen + 8'(WIDTH_RATIO)) / 8'(WIDTH_RATIO)) - 8'd1`
2. Write DOWNSIZE: `((int_awlen + 8'd1) * 8'(WIDTH_RATIO)) - 8'd1`
3. Read UPSIZE: `((int_arlen + 8'(WIDTH_RATIO)) / 8'(WIDTH_RATIO)) - 8'd1`
4. Read DOWNSIZE: `((int_arlen + 8'd1) * 8'(WIDTH_RATIO)) - 8'd1`

### Is This a Problem?

**NO - Here's why:**

1. **Self-Documenting:**
   ```systemverilog
   // Current (CLEAR):
   assign m_axi_awlen = ((int_awlen + 8'd1) * 8'(WIDTH_RATIO)) - 8'd1;

   // With function (OBSCURE):
   assign m_axi_awlen = calc_downsize_burst_len(int_awlen, WIDTH_RATIO);
   ```
   Reader immediately sees the math vs. having to lookup function.

2. **Formula is Verified:**
   Once we verify `(len+1)*ratio - 1` is correct, copy-paste is safe.

3. **Easy to Test:**
   Both converters have independent tests that validate the formula.

4. **Inline is Faster:**
   No function call overhead (even if inlined by synthesis).

---

## If You Still Want to Share Code...

### Minimal Viable Sharing

If you MUST extract common code, do this:

```systemverilog
// File: axi4_dwidth_converter_common.svh

// Burst length conversion formulas (just documentation, not code!)
//
// UPSIZE (narrow→wide):   master_len = (slave_len + ratio) / ratio - 1
// DOWNSIZE (wide→narrow): master_len = (slave_len + 1) * ratio - 1
//
// Examples (32→128, ratio=4):
//   Slave: 8 beats (len=7) → Master: 2 beats (len=1)  [UPSIZE: (7+4)/4-1 = 1]
//   Slave: 2 beats (len=1) → Master: 8 beats (len=7)  [DOWNSIZE: (1+1)*4-1 = 7]

// Address alignment for UPSIZE mode
`define ALIGN_ADDR(addr, align_bits) \
    {addr[AXI_ADDR_WIDTH-1:align_bits], {align_bits{1'b0}}}

// Burst length conversions (inline for readability)
`define UPSIZE_BURST_LEN(slave_len, ratio) \
    (((slave_len) + 8'(ratio)) / 8'(ratio)) - 8'd1

`define DOWNSIZE_BURST_LEN(slave_len, ratio) \
    (((slave_len) + 8'd1) * 8'(ratio)) - 8'd1
```

**Usage:**
```systemverilog
`include "axi4_dwidth_converter_common.svh"

assign m_axi_awlen = `DOWNSIZE_BURST_LEN(int_awlen, WIDTH_RATIO);
assign aligned_addr = `ALIGN_ADDR(int_awaddr, ALIGN_BITS);
```

**But even this is questionable** - it hides simple arithmetic behind macros.

---

## Conclusion

### Final Verdict: **Keep Current Architecture**

**Reasons:**
1. **Code is already clean** - separate read/write converters with clear logic
2. **Duplication is minimal** - <50 lines of truly duplicated code
3. **Abstraction adds complexity** - functions/macros make code harder to follow
4. **No real benefit** - saving 50 lines in 900-line codebase = 5.5% reduction
5. **Maintenance risk** - shared code means coupled changes

### What Makes Good Abstraction?

Extract common code when:
- ✅ Duplicated in ≥3 places (Rule of Three)
- ✅ Complex logic (>20 lines per instance)
- ✅ Frequently changing (evolving algorithm)
- ✅ Error-prone (easy to get wrong)

Our case:
- ❌ Only 2 instances (read + write)
- ❌ Simple logic (arithmetic formulas)
- ❌ Stable (AXI4 spec is frozen)
- ❌ Obvious (hard to get wrong)

### Better Investment of Time

Instead of extracting common code, invest in:
1. **Comprehensive tests** - verify both converters work correctly
2. **Documentation** - explain burst length formulas
3. **Assertions** - add SVA to catch protocol violations
4. **Performance analysis** - measure latency and throughput

---

**Analysis By:** Claude Code
**Repository:** RTL Design Sherpa
**Date:** 2025-10-24
**Conclusion:** Intuition was wrong - abstraction would harm clarity
