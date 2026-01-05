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

# Johnson-to-Binary Converter (`grayj2bin.sv`)

## Purpose
Converts Johnson counter codes to binary representation for use in asynchronous FIFOs with non-power-of-2 depths. Unlike standard Gray-to-binary conversion, this module handles the unique properties of Johnson counter sequences.

## Ports

### Input Ports
- **`clk`** - Clock signal (required for leading/trailing one detection)
- **`rst_n`** - Active-low reset
- **`gray[JCW-1:0]`** - Johnson counter input (misleadingly named "gray")

### Output Ports
- **`binary[WIDTH-1:0]`** - Binary output representing position in sequence

### Parameters
- **`JCW`** - Johnson Counter Width (equals FIFO DEPTH)
- **`WIDTH`** - Binary output width (typically `$clog2(DEPTH) + 1`)
- **`INSTANCE_NAME`** - String identifier for debug

## Johnson Counter Sequence Review

### Johnson Counter Characteristics
Johnson counters are **shift registers with inverted feedback**:

```
For JCW=6 (DEPTH=6):
State 0:  000000  ← Initial state
State 1:  100000  ← Shift left, insert 1
State 2:  110000
State 3:  111000  
State 4:  111100
State 5:  111110
State 6:  111111  ← All 1s (special case)
State 7:  011111  ← Shift left, insert ~MSB (0)
State 8:  001111
State 9:  000111
State 10: 000011
State 11: 000001
State 0:  000000  ← Cycle complete (12 states total)
```

### Key Properties
- **Single bit transitions**: Only one bit changes per state
- **Two phases**: 
  - **First half** (0 to DEPTH-1): Filling with 1s from left
  - **Second half** (DEPTH to 2×DEPTH-1): Emptying 1s from left
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
    .WIDTH(JCW),
    .INSTANCE_NAME(INSTANCE_NAME)
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
Johnson: 001111 (w_leading_one = 5, w_trailing_one = 2)
Logic: First half, so position = w_leading_one + 1 = 5 + 1 = 6
Binary: 000110 (with MSB=0 indicating first half)
```

### Second Half Conversion (MSB = 1)  
```
Johnson: 111000 (w_leading_one = 0, w_trailing_one = 2)
Logic: Second half, so position = w_trailing_one = 2
Binary: 100010 (with MSB=1 indicating second half)
```

### Special Cases
```
Johnson: 000000 → Binary: 000000 (all zeros case)
Johnson: 111111 → Binary: 000000 (all ones case - same as zeros)
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
// fifo_async_div2.sv usage:
grayj2bin #(
    .JCW(JCW),                    // = DEPTH
    .WIDTH(AW + 1),               // Address width + wrap bit
    .INSTANCE_NAME("rd_ptr_gray2bin_inst")
) rd_ptr_gray2bin_inst(
    .binary(w_wdom_rd_ptr_bin),   // Binary for arithmetic
    .gray(r_wdom_rd_ptr_gray),    // Johnson counter from CDC
    .clk(wr_clk),
    .rst_n(wr_rst_n)
);
```

### Why Clock is Required
Unlike pure combinational Gray-to-binary conversion, Johnson-to-binary needs the `leading_one_trailing_one` helper, which may use sequential logic for complex position detection.

## Comparison with Standard Gray2Bin

| Aspect | Standard Gray2Bin | Johnson2Bin (grayj2bin) |
|--------|-------------------|--------------------------|
| **Input type** | Traditional Gray code | Johnson counter sequence |
| **Algorithm** | XOR reduction | Position detection |
| **Complexity** | Simple combinational | Complex position logic |
| **Clock requirement** | None | Required for helper modules |
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
- **fifo_async_div2**: Primary user of this conversion
- **gray2bin**: Standard Gray-to-binary for comparison
- **fifo_control**: Uses converted binary values for status generation

## Advanced Topics

### Hierarchical Johnson Counters
For very large depths, consider hierarchical approach:
```systemverilog
// Break large Johnson counter into smaller segments
// Use multiple grayj2bin instances with higher-level arbitration
```

### Alternative Position Detection
Some implementations use different position detection algorithms:
- **Priority encoders**: Find first/last set bit
- **Thermometer decoders**: Convert 1-hot positions
- **LUT-based**: For small, fixed widths

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
