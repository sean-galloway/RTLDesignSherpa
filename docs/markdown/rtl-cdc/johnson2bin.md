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

# Johnson-to-Binary Converter (`johnson2bin.sv`)

## Purpose
Converts Johnson counter codes to binary representation for use in asynchronous FIFOs with non-power-of-2 depths. Unlike standard Gray-to-binary conversion, this module handles the unique properties of Johnson counter sequences.

## Ports

### Input Ports
- **`clk`** - Clock input. Declared but unused; the module is combinational.
- **`rst_n`** - Active-low reset. Declared but unused; the module is combinational.
- **`gray[JCW-1:0]`** - Johnson counter input (misleadingly named "gray")

### Output Ports
- **`binary[WIDTH-1:0]`** - Binary output representing position in sequence

### Parameters
- **`JCW`** - Johnson Counter Width (equals FIFO DEPTH)
- **`WIDTH`** - Binary output width (typically `$clog2(DEPTH) + 1`)

## Johnson Counter Sequence Review

### Johnson Counter Characteristics
Johnson counters are **shift registers with inverted feedback**:

```
For JCW=6 (DEPTH=6):
State 0:  000000  ← Initial state
State 1:  000001  ← Shift left, insert ~MSB (1)
State 2:  000011
State 3:  000111
State 4:  001111
State 5:  011111
State 6:  111111  ← All 1s (fill complete)
State 7:  111110  ← Shift left, insert ~MSB (0)
State 8:  111100
State 9:  111000
State 10: 110000
State 11: 100000
State 0:  000000  ← Cycle complete (12 states total)
```

> **Fill direction.** This library shifts in at the LSB. `counter_johnson.sv`
> implements `counter_gray <= {counter_gray[WIDTH-2:0], ~counter_gray[WIDTH-1]}`,
> so ones enter at bit 0 and march upward. An earlier revision of this page showed
> the mirror image (ones entering at the MSB), which is also a valid Johnson
> counter but is *not* the one this library builds -- and both worked conversion
> examples inherited the error. Note that external references frequently use the
> MSB-fill convention, so check against `counter_johnson.sv` rather than against
> a textbook.


### Key Properties
- **Single bit transitions**: Only one bit changes per state
- **Two phases**: 
  - **First half** (0 to DEPTH-1): Filling with 1s from the **right** (ones
    enter at bit 0 and march upward: 000000 → 000001 → 000011 → ...)
  - **Second half** (DEPTH to 2×DEPTH-1): Emptying 1s from the **right**
    (111111 → 111110 → 111100 → ...)
- **Wrap indicator**: MSB indicates which half of cycle

## Conversion Algorithm

### Strategy Overview
The conversion uses **position detection** of the transition between 1s and 0s:

```systemverilog
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

### Position Detection Module
```systemverilog
leading_one_trailing_one #(
    .WIDTH(JCW)
) u_leading_one_trailing_one (
    .data(gray),
    .leadingone(w_leading_one),
    .trailingone(w_trailing_one),
    .all_zeroes(w_all_zeroes),
    .all_ones(w_all_ones),
    .valid(w_valid)
);
```

## Detailed Conversion Examples

### First Half Conversion (MSB = 0)
```
Johnson: 001111 (set bits {0,1,2,3}: w_leading_one = 3, w_trailing_one = 0)
Logic: gray[5]=0 → first half, position = w_leading_one + 1 = 3 + 1 = 4
Binary: 000100 (MSB=0 indicating first half) = state 4
```

### Second Half Conversion (MSB = 1)  
```
Johnson: 111000 (set bits {3,4,5}: w_leading_one = 5, w_trailing_one = 3)
Logic: gray[5]=1 → second half, position = w_trailing_one = 3
Binary: 100011 (MSB=1 indicating second half) = state 9 (6 + 3)
```

### Special Cases
```
Johnson: 000000 → Binary: 000000 (all zeros case)
Johnson: 111111 → Binary: 100000 (all ones: lower bits forced to 0, but the RTL
         unconditionally sets binary[WIDTH-1] = gray[JCW-1] = 1, so the wrap
         bit is SET -- this is {wrap=1, addr=0}, NOT the same as all-zeros.
         FIFO full detection depends on this.)
```

## Implementation Deep Dive

### Three-Part Binary Construction
```systemverilog
assign binary[WIDTH-1]   = gray[JCW-1];                 // MSB = wrap indicator
assign binary[WIDTH-2:0] = w_binary[WIDTH-2:0];         // Lower bits = position
```

### Width Calculations
```systemverilog
localparam int N = $clog2(JCW);                         // Address bits needed
localparam int PAD_WIDTH = (WIDTH > N+1) ? WIDTH-N-1 : 0; // Padding if needed
```

### Why This Algorithm Works

#### First Half Logic (MSB = 0)
- **Pattern**: `000...0111...1` (0s followed by 1s)
- **Leading one**: Position of leftmost 1
- **Conversion**: Position = leading_one + 1
- **Reasoning**: We've filled (leading_one + 1) positions with 1s

#### Second Half Logic (MSB = 1)
- **Pattern**: `111...1000...0` (1s followed by 0s)  
- **Trailing one**: Position of rightmost 1
- **Conversion**: Position = trailing_one
- **Reasoning**: We're emptying from the left, trailing_one shows how far

## Use in Asynchronous FIFO

### Context in FIFO Operation
```systemverilog
// fifo_async.sv (USE_JOHNSON=1) usage:
johnson2bin #(
    .JCW(JCW),                    // = DEPTH
    .WIDTH(AW + 1)                // Address width + wrap bit
) rd_ptr_gray2bin_inst(
    .binary(w_wdom_rd_ptr_bin),   // Binary for arithmetic
    .gray(r_wdom_rd_ptr_gray),    // Johnson counter from CDC
    .clk(wr_clk),
    .rst_n(wr_rst_n)
);
```

### The clock and reset ports are unused

`johnson2bin` declares `clk` and `rst_n` but **never uses them**. The conversion
is entirely combinational: a single `always_comb` block driven by
`leading_one_trailing_one`, which is itself combinational (one `always_comb` plus
continuous assignments, no `always_ff` anywhere).

The ports are retained so the module can be dropped into a clocked context
without an interface change, and so a future revision could register the output
without breaking callers. Tie them off to whatever the surrounding domain uses;
nothing in this module samples them. Do not expect a cycle of latency -- the
output follows `gray` combinationally, and long conversion paths must be
registered by the caller.

## Comparison with Standard Gray2Bin

| Aspect | Standard Gray2Bin | Johnson2Bin (johnson2bin) |
|--------|-------------------|--------------------------|
| **Input type** | Traditional Gray code | Johnson counter sequence |
| **Algorithm** | XOR reduction | Position detection |
| **Complexity** | Simple combinational | Complex position logic |
| **Clock requirement** | None | None (clk/rst_n ports exist but are unused) |
| **Width scaling** | Logarithmic | Linear with JCW |
| **Use case** | Power-of-2 sequences | Any even sequences |

## Performance Characteristics

### Timing Analysis
- **Critical path**: Through position detection logic
- **Delay components**: 
  - Leading/trailing one detection
  - Binary arithmetic (addition)
  - Output multiplexing
- **Synthesis complexity**: Higher than standard Gray conversion

### Resource Utilization
```
Resources scale with JCW (Johnson Counter Width):
- Small FIFOs (JCW ≤ 16): Reasonable overhead
- Medium FIFOs (JCW = 32-64): Significant resources  
- Large FIFOs (JCW > 64): May become limiting factor
```

## Design Considerations

### When to Use Johnson vs. Gray
```systemverilog
// Use Johnson counter approach when:
parameter int DEPTH = 10;  // Non-power-of-2 required
parameter int DEPTH = 6;   // Specific size needed
parameter int DEPTH = 14;  // Standard Gray won't work

// Use standard Gray approach when:
parameter int DEPTH = 8;   // Power-of-2 is acceptable
parameter int DEPTH = 16;  // Efficiency more important  
parameter int DEPTH = 64;  // Large depth, resource conscious
```

### Resource Planning
```systemverilog
// Resource overhead estimation:
// Standard Gray: ~log2(DEPTH) XOR gates
// Johnson: ~DEPTH comparators + position logic

// Break-even point typically around DEPTH = 16-32
```

### Verification Challenges
```systemverilog
// More complex verification due to:
// 1. Two-phase sequence behavior
// 2. Position detection correctness
// 3. Special case handling (all 0s, all 1s)
// 4. Wraparound boundary conditions
```

## Error Conditions and Debug

### Invalid Johnson Sequences
The `leading_one_trailing_one` module provides validation:
```systemverilog
.valid(w_valid)  // Indicates valid Johnson pattern
```

Valid Johnson patterns have exactly one transition from 1s to 0s (or vice versa).

### Debug Visibility
```systemverilog
// Monitor internal state for debugging:
// - w_leading_one: Position of leftmost 1
// - w_trailing_one: Position of rightmost 1  
// - w_all_zeroes: Special case flag
// - w_all_ones: Special case flag
// - w_valid: Sequence validity
```

### Common Issues
1. **Invalid sequences**: Non-Johnson patterns on input
2. **Width mismatches**: JCW vs. actual Johnson counter width
3. **Phase confusion**: Misunderstanding first vs. second half logic
4. **Boundary conditions**: All-zeros and all-ones handling

## Related Modules
- **counter_johnson**: Generates Johnson counter sequences
- **leading_one_trailing_one**: Position detection helper
- **fifo_async / gaxi_fifo_async (USE_JOHNSON=1)**: Primary users of this conversion
- **gray2bin**: Standard Gray-to-binary for comparison
- **fifo_control**: Uses converted binary values for status generation

## Advanced Topics

### Hierarchical Johnson Counters
For very large depths, consider hierarchical approach:
```systemverilog
// Break large Johnson counter into smaller segments
// Use multiple johnson2bin instances with higher-level arbitration
```

### Alternative Position Detection
Some implementations use different position detection algorithms:
- **Priority encoders**: Find first/last set bit
- **Thermometer decoders**: Convert 1-hot positions
- **LUT-based**: For small, fixed widths

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
