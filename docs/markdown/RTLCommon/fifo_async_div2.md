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

# Asynchronous FIFO - Divisible by 2 (`fifo_async_div2.sv`)

## Purpose
Implements an asynchronous FIFO for clock domain crossing that **works with any even depth** (not restricted to powers of 2). Uses Johnson counters instead of traditional Gray codes for pointer management.

## Ports

### Write Domain
- **`wr_clk`** - Write domain clock
- **`wr_rst_n`** - Write domain active-low reset
- **`write`** - Write enable signal
- **`wr_data[DATA_WIDTH-1:0]`** - Data to write
- **`wr_full`** - Write domain full flag
- **`wr_almost_full`** - Write domain almost full flag

### Read Domain
- **`rd_clk`** - Read domain clock
- **`rd_rst_n`** - Read domain active-low reset
- **`read`** - Read enable signal
- **`rd_data[DATA_WIDTH-1:0]`** - Data read from FIFO
- **`rd_empty`** - Read domain empty flag
- **`rd_almost_empty`** - Read domain almost empty flag

### Parameters
- **`REGISTERED`** - 0=mux mode, 1=flop mode for read output
- **`DATA_WIDTH`** - Width of data (default: 8)
- **`DEPTH`** - FIFO depth - **any even number** (default: 10)
- **`N_FLOP_CROSS`** - Number of synchronizer stages (default: 2)
- **`ALMOST_WR_MARGIN`** - Almost full threshold (default: 1)
- **`ALMOST_RD_MARGIN`** - Almost empty threshold (default: 1)

## Architecture Overview

The key innovation is the **hybrid pointer system**:

```
Write Domain                           Read Domain
┌─────────────┐                       ┌─────────────┐
│ Binary      │                       │ Binary      │
│ Counter     │                       │ Counter     │
│     +       │                       │     +       │
│ Johnson ────┼──→ Johnson ───────────┼──→ Sync ────┼──→ Johnson2Bin │
│ Counter     │   Code               │   Chain     │               │
└─────────────┘                       └─────────────┘
```

## Johnson Counter Deep Dive

### What are Johnson Counters?
Johnson counters are **shift registers with inverted feedback**:

```
For DEPTH=6:
State 0: 000000
State 1: 100000  ← shift left, insert 1
State 2: 110000
State 3: 111000
State 4: 111100
State 5: 111110
State 6: 111111
State 7: 011111  ← shift left, insert ~MSB (0)
State 8: 001111
State 9: 000111
State 10: 000011
State 11: 000001
State 12: 000000 ← back to start
```

### Johnson vs. Gray Code Comparison

| Aspect | Gray Code (fifo_async) | Johnson Counter (fifo_async_div2) |
|--------|------------------------|-----------------------------------|
| **Counter Width** | `$clog2(DEPTH) + 1` | `DEPTH` bits |
| **Depth Restriction** | Powers of 2 only | Any even number |
| **State Sequence** | Binary Gray pattern | One-hot rotation |
| **Memory Efficiency** | Logarithmic growth | Linear growth |
| **CDC Safety** | Single bit transitions | Single bit transitions |
| **Conversion Complexity** | Simple XOR tree | Complex position detection |

## Implementation Details

### Dual Counter Architecture

#### Binary Counters for Control
```systemverilog
counter_bin #(
    .MAX(D),
    .WIDTH(AW + 1)
) wr_ptr_counter_bin(
    .clk(wr_clk),
    .rst_n(wr_rst_n),
    .enable(write && !wr_full),
    .counter_bin_next(w_wr_ptr_bin_next),
    .counter_bin_curr(r_wr_ptr_bin)
);
```

#### Johnson Counters for CDC
```systemverilog
counter_johnson #(
    .WIDTH(JCW)  // JCW = DEPTH
) wr_ptr_counter_gray(
    .clk(wr_clk),
    .rst_n(wr_rst_n),
    .enable(write && !wr_full),
    .counter_gray(r_wr_ptr_gray)  // Johnson code output
);
```

### Why Both Counter Types?

#### Binary Counters Used For:
- **Memory addressing**: Direct binary-to-address mapping
- **Occupancy calculation**: Standard arithmetic operations
- **Almost full/empty logic**: Numerical comparisons

#### Johnson Counters Used For:
- **Clock domain crossing**: Safe single-bit transitions
- **Synchronization**: Metastability-resistant transitions
- **Wrap detection**: Clear sequence boundaries

## Johnson-to-Binary Conversion

### Conversion Challenge
Converting Johnson counter states back to binary addresses requires **position detection**:

```systemverilog
// Johnson state: 111100000 (for DEPTH=10)
// Need to find: position of transition (leading 1s to trailing 0s)
// Result: Binary address for memory access
```

### `grayj2bin` Module Implementation
```systemverilog
// Key conversion logic
if (w_all_zeroes || w_all_ones) begin
    w_binary = {WIDTH{1'b0}};
end else if (gray[JCW-1]) begin
    // Second half: use leading one position directly  
    w_binary = {{(WIDTH-N){1'b0}}, w_trailing_one};
end else begin
    // First half: use trailing one + 1
    w_binary = {{(WIDTH-N){1'b0}}, (w_leading_one + 1'b1)};
end
```

### Leading/Trailing One Detection
The conversion relies on `leading_one_trailing_one` module:
- **Leading one**: Position of leftmost '1' bit
- **Trailing one**: Position of rightmost '1' bit  
- **All zeros/ones**: Special case handling
- **Valid flag**: Ensures proper Johnson sequence

## Flexible Depth Support

### Even Number Requirement
Johnson counters naturally support even depths because:
- **Sequence length**: 2 × DEPTH states in full cycle
- **Half cycles**: Each half contains DEPTH unique states
- **Symmetry**: Clean wraparound behavior

### Example Depth Flexibility
```systemverilog
// Valid depths for fifo_async_div2:
parameter int DEPTH = 6;   // ✓ (even)
parameter int DEPTH = 10;  // ✓ (even)  
parameter int DEPTH = 14;  // ✓ (even)
parameter int DEPTH = 100; // ✓ (even)

// Invalid depths:
parameter int DEPTH = 7;   // ✗ (odd)
parameter int DEPTH = 15;  // ✗ (odd)
```

### vs. Power-of-2 Restriction
```systemverilog
// fifo_async valid depths: 2, 4, 8, 16, 32, 64, ...
// fifo_async_div2 valid depths: 2, 4, 6, 8, 10, 12, 14, 16, 18, ...
```

## Memory Efficiency Trade-offs

### Resource Usage Comparison

| FIFO Depth | Gray Code Width | Johnson Width | Efficiency Ratio |
|-------------|-----------------|---------------|------------------|
| 4           | 3 bits         | 4 bits        | 1.33× |
| 8           | 4 bits         | 8 bits        | 2.00× |
| 16          | 5 bits         | 16 bits       | 3.20× |
| 32          | 6 bits         | 32 bits       | 5.33× |
| 64          | 6 bits         | 64 bits       | 10.67× |

### When to Choose Each Approach

#### Choose `fifo_async` (Gray Code) When:
- **Large depths**: >32 words (better resource efficiency)
- **Standard depths**: Powers of 2 are acceptable
- **Resource constrained**: Minimizing logic usage critical

#### Choose `fifo_async_div2` (Johnson) When:
- **Specific depths**: Need exact non-power-of-2 sizes
- **Small to medium depths**: <32 words (manageable overhead)
- **System requirements**: Exact depth matching critical

## Clock Domain Crossing Details

### Synchronization Strategy
Same multi-stage synchronizer approach as Gray code version:

```systemverilog
glitch_free_n_dff_arn #(
    .FLOP_COUNT(N_FLOP_CROSS),
    .WIDTH(JCW)  // Note: wider than Gray code version
) rd_ptr_gray_cross_inst(
    .q(r_wdom_rd_ptr_gray),
    .d(r_rd_ptr_gray),
    .clk(wr_clk),
    .rst_n(wr_rst_n)
);
```

### Metastability Protection
- **Single bit transitions**: Johnson counters guarantee this
- **Multi-stage sync**: Standard 2-3 stage synchronizers
- **Conversion timing**: Johnson-to-binary happens after synchronization

## Use Cases

### Ideal Applications
- **Video buffers**: Need specific line/frame buffer sizes
- **Audio processing**: Exact sample count requirements  
- **Protocol buffers**: Match specific packet/frame sizes
- **Memory interfaces**: Align with specific burst lengths

### Application Examples
```systemverilog
// Video line buffer (1920 pixels)
fifo_async_div2 #(.DEPTH(1920)) line_buffer (...);

// Audio sample buffer (48 samples)  
fifo_async_div2 #(.DEPTH(48)) audio_buffer (...);

// Packet buffer (1500 bytes)
fifo_async_div2 #(.DEPTH(1500)) packet_buffer (...);
```

## Performance Characteristics

### Throughput
- **Same as Gray version**: 1 operation per clock per domain
- **No performance penalty**: CDC latency identical

### Resource Usage
- **Higher logic usage**: Linear scaling with depth
- **Same memory usage**: Identical memory array
- **Conversion overhead**: Additional logic for Johnson-to-binary

### Timing
- **CDC latency**: Same 2-3 cycle synchronizer delay
- **Conversion delay**: Additional combinational path
- **Critical paths**: May be longer due to conversion logic

## Design Considerations

### Depth Selection Guidelines
- **Small depths (<32)**: Consider div2 for exact sizing
- **Large depths (>64)**: Prefer power-of-2 for efficiency
- **Medium depths**: Evaluate specific size vs. efficiency needs

### Resource Planning
- **Logic overhead**: Budget for Johnson counter width
- **Timing closure**: Account for conversion logic delay
- **Power consumption**: Wider counters consume more power

## WaveDrom Visualization

**High-quality waveforms showcasing Johnson counter CDC mechanism are available!**

Run the WaveDrom test to generate detailed timing diagrams:

```bash
# Generate Johnson counter waveforms (showcases unique CDC implementation)
pytest val/common/test_fifo_async_div2_wavedrom.py -v
```

**Waveform Scenarios Generated:**

1. **Write-Fill-Read-Empty Cycle**
   - Complete FIFO lifecycle
   - Johnson counter state progression
   - Flag transitions (wr_full, rd_empty)
   - Demonstrates end-to-end operation

2. **Cross-Domain Synchronization** ⭐ **KEY SCENARIO**
   - Johnson counter transitions (single-bit changes only)
   - Write pointer sync from wr_clk to rd_clk domain
   - Read pointer sync from rd_clk to wr_clk domain
   - CDC latency visualization
   - **THIS IS THE UNIQUE FEATURE** distinguishing from Gray code

3. **Back-to-Back Operations**
   - Dual pointer architecture in action
   - Binary pointers for memory addressing
   - Johnson pointers for CDC safety
   - Simultaneous read/write capability

4. **Almost-Full/Almost-Empty Flags**
   - Flow control signaling
   - Threshold-based flag assertion
   - Proactive backpressure indication

**What Makes These Waveforms Special:**

The test specifically highlights the **Johnson counter CDC mechanism** which is the unique differentiator of `fifo_async_div2`:

- **Johnson Counter States**: Shows the one-hot-like rotation pattern
- **Single-Bit Transitions**: Demonstrates CDC safety (only one bit changes at a time)
- **Even-Depth Flexibility**: Works with depths like 6, 10, 14 (not just powers of 2)
- **Dual Pointer System**: Binary for addressing, Johnson for CDC

**Comparison with Standard Async FIFO:**

For comparison, also see:
- `test_fifo_async_wavedrom.py` - Standard Gray code CDC (power-of-2 depths)
- `test_fifo_sync_wavedrom.py` - Synchronous FIFO (single clock, no CDC)

## Error Detection
Same simulation-based error checking as other FIFO variants:
- Write-while-full detection
- Read-while-empty detection
- Timing-aware error reporting

## Related Modules
- **fifo_async**: Power-of-2 version using Gray codes
- **counter_johnson**: Johnson counter implementation
- **grayj2bin**: Johnson-to-binary converter
- **leading_one_trailing_one**: Position detection helper

## Test and Verification

**Comprehensive Test Suite:**
- `val/common/test_fifo_buffer_async_div2.py` - Full functional verification
- `val/common/test_fifo_async_div2_wavedrom.py` - WaveDrom timing diagrams ⭐

**Run Tests:**
```bash
# Full functional test (basic/medium/full levels)
pytest val/common/test_fifo_buffer_async_div2.py -v

# WaveDrom waveform generation
pytest val/common/test_fifo_async_div2_wavedrom.py -v
```

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
