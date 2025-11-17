# Dual-Buffer Implementation for axi_data_dnsize

**Date:** 2025-10-25
**Purpose:** Document the dual-buffer feature implementation for high-throughput data width conversion

---

## Executive Summary

Added optional dual-buffer mode to `axi_data_dnsize.sv` module to achieve **100% throughput** for continuous data streams.

**Key Results:**
- **Single-buffer mode (DUAL_BUFFER=0):** 80% throughput, 1-cycle dead time per wide beat
- **Dual-buffer mode (DUAL_BUFFER=1):** 100% throughput, zero dead cycles
- **Area cost:** Approximately 2× buffer registers (+100% overhead)
- **Compatibility:** Fully backward compatible, works with all existing test configurations

---

## Architecture Overview

### Single-Buffer Mode (DUAL_BUFFER=0)

**Structure:**
```
┌─────────────────┐
│  r_data_buffer  │  ← ONE wide beat buffered
│  (WIDE_WIDTH)   │
└─────────────────┘
     ↓
  Split into
  narrow beats
```

**Throughput Limitation:**
- Must wait for ALL narrow beats to complete before accepting next wide beat
- 1-cycle gap when transitioning between wide beats
- Throughput = 4/(4+1) = 80% for 4:1 ratio

### Dual-Buffer Mode (DUAL_BUFFER=1)

**Structure:**
```
┌─────────────┐
│  r_buffer_0  │  ← Splitting into narrow beats
│              │
└─────────────┘
     ↓ (reading)

┌─────────────┐
│  r_buffer_1  │  ← Accepting NEXT wide beat
│              │
└─────────────┘
     ↑ (writing)
```

**Ping-Pong Operation:**
1. Buffer 0 splits while Buffer 1 accepts new data
2. When Buffer 0 completes, swap: Buffer 1 splits, Buffer 0 accepts
3. Continuous operation with no dead cycles

**Throughput:** 100% (4/4) for any ratio

---

## Implementation Details

### New Parameter

```systemverilog
parameter int DUAL_BUFFER = 0,  // 0=single buffer (80% throughput, area efficient)
                                // 1=dual buffer (100% throughput, 2× area)
```

### State Variables

**Single-Buffer Mode:**
```systemverilog
logic [WIDE_WIDTH-1:0]          r_data_buffer;
logic [WIDE_SB_PORT_WIDTH-1:0]  r_sideband_buffer;
logic                           r_wide_buffered;
logic                           r_last_buffered;
```

**Dual-Buffer Mode:**
```systemverilog
logic [WIDE_WIDTH-1:0]          r_buffer_0, r_buffer_1;
logic [WIDE_SB_PORT_WIDTH-1:0]  r_sb_buffer_0, r_sb_buffer_1;
logic                           r_last_buffer_0, r_last_buffer_1;
logic                           r_buffer_0_valid, r_buffer_1_valid;
logic                           r_read_buffer;  // 0=reading buf0, 1=reading buf1
```

### Write Path (DUAL_BUFFER=1)

```systemverilog
if (wide_valid && wide_ready) begin
    if (!gen_dual_buffer.r_buffer_0_valid) begin
        // Write to buffer 0
        gen_dual_buffer.r_buffer_0 <= wide_data;
        gen_dual_buffer.r_buffer_0_valid <= 1'b1;
    end else begin
        // Write to buffer 1 (must be empty if wide_ready=1)
        gen_dual_buffer.r_buffer_1 <= wide_data;
        gen_dual_buffer.r_buffer_1_valid <= 1'b1;
    end
end
```

**Key:** Always write to the empty buffer.

### Read Path (DUAL_BUFFER=1)

```systemverilog
// Read from current buffer
if (current_buffer_valid && narrow_ready) begin
    if (is_last_narrow_beat) begin
        // Clear current buffer's valid flag
        if (gen_dual_buffer.r_read_buffer)
            gen_dual_buffer.r_buffer_1_valid <= 1'b0;
        else
            gen_dual_buffer.r_buffer_0_valid <= 1'b0;

        // Swap to other buffer if it has data
        if (other_buffer_valid)
            gen_dual_buffer.r_read_buffer <= ~gen_dual_buffer.r_read_buffer;
    end
end
```

**Key:** On last narrow beat, clear current buffer and swap to other if available.

### Ready Logic

**Single-Buffer:**
```systemverilog
assign wide_ready = !r_wide_buffered || (narrow_ready && w_last_narrow_beat);
```
- Ready when buffer empty OR sending last narrow beat (1-cycle early)

**Dual-Buffer:**
```systemverilog
assign wide_ready = !r_buffer_0_valid || !r_buffer_1_valid;
```
- Ready when **at least one** buffer is empty
- Allows continuous acceptance

---

## Burst Tracking Integration

Dual-buffer mode **fully supports** burst tracking (TRACK_BURSTS=1):

**Challenge:** Track burst position across buffer swaps

**Solution:** Shared burst counter applies to whichever buffer is currently being read:
```systemverilog
// Burst tracking state (shared between buffers)
logic [BURST_LEN_WIDTH-1:0] r_slave_beat_count;
logic [BURST_LEN_WIDTH-1:0] r_slave_total_beats;
logic                       r_burst_active;

// Applies to current read buffer
if (((r_slave_beat_count + 1'b1) >= r_slave_total_beats)) begin
    // Last narrow beat of entire burst
    // Clear current buffer and end burst
end
```

**Result:** LAST signal correctly generated on final beat of burst, regardless of buffer swapping.

---

## Resource Impact

### Area Analysis (128-bit Wide, 32-bit Narrow, 16-bit Sideband)

| Resource | Single Buffer | Dual Buffer | Overhead |
|----------|--------------|-------------|----------|
| Data registers | 128 bits | 256 bits | +128 bits |
| Sideband registers | 16 bits | 32 bits | +16 bits |
| LAST flags | 1 bit | 2 bits | +1 bit |
| Valid flags | 1 bit | 2 bits | +1 bit |
| Read selector | - | 1 bit | +1 bit |
| **Total FFs** | **146** | **292** | **+146 (+100%)** |

**Control Logic:** ~30% increase (buffer selection, swap logic)

**Overall:** Expect ~100% area increase for dual-buffer mode.

### Performance Impact

| Mode | Throughput (4:1 Ratio) | Cycles/Wide Beat | Utilization |
|------|------------------------|------------------|-------------|
| Single-Buffer | 80% | 5 (4 active + 1 dead) | 4/5 |
| Dual-Buffer | 100% | 4 (4 active + 0 dead) | 4/4 |

**Improvement:** +25% throughput (from 80% to 100%)

---

## Test Coverage

### Test Configurations Added

All existing test configurations now have dual-buffer variants:

**Single-Buffer Tests (DUAL_BUFFER=0):**
- 128to32_wstrb_slice_simple
- 256to64_wstrb_slice_simple
- 128to32_rresp_broadcast_simple
- 256to64_rresp_broadcast_simple
- 128to32_rresp_burst_track
- 256to64_rresp_burst_track
- 512to128_rresp_burst_track
- 128to64_no_sideband_simple

**Dual-Buffer Tests (DUAL_BUFFER=1):**
- Same configurations with "_DUAL" suffix
- Total: 16 test configurations

### Verification Results

**Tested:**
- ✅ Basic data splitting (all ratios)
- ✅ Sideband handling (broadcast and slice modes)
- ✅ Burst tracking with LAST generation
- ✅ Backpressure handling
- ✅ Continuous streaming

**Result:** All tests PASS for both single and dual-buffer modes.

---

## Usage Recommendations

### When to Use Single-Buffer Mode (DUAL_BUFFER=0)

✅ **Use when:**
- Area is critical
- Throughput requirements are <100%
- Source/sink have natural gaps in traffic
- Design is already bottlenecked elsewhere

**Example:** Write path downsize where upstream has occasional pauses

### When to Use Dual-Buffer Mode (DUAL_BUFFER=1)

✅ **Use when:**
- Maximum throughput required
- Continuous streaming data
- Sufficient area budget
- Critical path in high-performance system

**Example:** High-bandwidth DMA engine with continuous transfers

---

## Code Example

### Instantiation: Single-Buffer Mode (Area Efficient)

```systemverilog
axi_data_dnsize #(
    .WIDE_WIDTH(512),
    .NARROW_WIDTH(128),
    .WIDE_SB_WIDTH(64),      // WSTRB
    .NARROW_SB_WIDTH(16),    // WSTRB
    .SB_BROADCAST(0),        // Slice mode
    .TRACK_BURSTS(0),        // Simple mode
    .DUAL_BUFFER(0)          // Single buffer (80% throughput)
) u_dnsize (
    .aclk(clk),
    .aresetn(rst_n),
    // ... ports
);
```

### Instantiation: Dual-Buffer Mode (High Throughput)

```systemverilog
axi_data_dnsize #(
    .WIDE_WIDTH(512),
    .NARROW_WIDTH(128),
    .WIDE_SB_WIDTH(64),
    .NARROW_SB_WIDTH(16),
    .SB_BROADCAST(0),
    .TRACK_BURSTS(0),
    .DUAL_BUFFER(1)          // Dual buffer (100% throughput)
) u_dnsize (
    .aclk(clk),
    .aresetn(rst_n),
    // ... ports
);
```

---

## Design Decisions

### Why Not Dual-Buffer for Upsize?

**axi_data_upsize already achieves 100% throughput** with single buffer:
- Can accept narrow beat while outputting wide beat simultaneously
- The `|| wide_ready` term in narrow_ready enables overlap
- No benefit from dual buffering

**Conclusion:** Dual-buffer only needed for dnsize module.

### Why Use Generate Blocks?

**Rationale:**
- Complete separation of single vs. dual-buffer logic
- No runtime overhead (compile-time selection)
- Easier to verify each mode independently
- Cleaner code structure

### Why Not Make Dual-Buffer the Default?

**Considerations:**
- 100% area overhead is significant
- Many use cases don't need 100% throughput
- Single-buffer is simpler and well-tested
- User can opt-in when needed

**Decision:** Default to DUAL_BUFFER=0, user explicitly enables when needed.

---

## Lessons Learned

### SystemVerilog Constraints

**Issue:** Cannot declare logic variables inside procedural blocks
```systemverilog
// ILLEGAL:
always_ff @(posedge clk) begin
    logic temp;  // ← NOT ALLOWED
    temp = ...;
end
```

**Solution:** Inline expressions or move declarations outside block

### Generate Block Naming

**Best Practice:** Use hierarchical naming for generate block signals:
```systemverilog
gen_dual_buffer.r_buffer_0_valid  // Clear which mode
gen_single_buffer.r_wide_buffered // Clear which mode
```

### Buffer Swap Logic

**Key Insight:** Swap only when:
1. Current buffer completes (last narrow beat sent)
2. Other buffer has valid data waiting

This prevents unnecessary swaps and maintains correct ordering.

---

## Future Enhancements

### Potential Improvements

1. **Configurable Buffer Depth:** Allow >2 buffers for even higher throughput
2. **Credit-Based Flow Control:** Integrate with upstream credit system
3. **Performance Counters:** Monitor buffer utilization, stalls
4. **Power Gating:** Disable unused buffer when not needed

### Alternative Architectures

**Skid Buffer Approach:**
- Insert skid buffers on outputs instead of dual data buffers
- Lower area overhead
- Similar throughput improvement

**FIFO Approach:**
- Replace buffers with small FIFOs
- More flexible depth control
- Higher area cost

---

## Summary

The dual-buffer implementation successfully provides an **optional high-throughput mode** for the `axi_data_dnsize` module:

✅ **Functionality:** Proven correct through comprehensive testing
✅ **Performance:** 100% throughput vs. 80% for single-buffer
✅ **Compatibility:** Fully backward compatible
✅ **Flexibility:** User-selectable via parameter
✅ **Robustness:** Works with all modes (broadcast, slice, burst tracking)

**Trade-off:** ~100% area increase for +25% throughput improvement

**Recommendation:** Use dual-buffer mode for performance-critical paths with continuous data flow.

---

## Related Files

- `projects/components/converters/rtl/axi_data_dnsize.sv` - RTL implementation
- `projects/components/converters/dv/tests/test_axi_data_dnsize.py` - Test suite
- `projects/components/converters/dv/tbclasses/axi_data_dnsize_tb.py` - Testbench class
- `projects/components/converters/USAGE.md` - Usage documentation
- `projects/components/converters/ANALYSIS_APB_CONVERTER.md` - APB converter analysis

**Author:** RTL Design Sherpa
**Date:** 2025-10-25
