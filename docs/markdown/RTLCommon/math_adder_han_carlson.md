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

# Han-Carlson Parallel Prefix Adder

A hybrid parallel prefix adder that combines the low wiring complexity of Brent-Kung with near-Kogge-Stone speed, providing an optimal balance of area, wire routing, and logic depth for advanced process nodes.

## Overview

The `math_adder_han_carlson` module family implements Han-Carlson parallel prefix adders. Han-Carlson is a "sparsity-2" architecture that computes prefix operations only on even bit positions in intermediate stages, then fills in odd positions in a final stage using area-efficient gray cells.

**Available widths:** 16-bit, 48-bit (auto-generated for BF16 arithmetic)

**Key Features:**
- **O(log N + 1) depth** - Only one level more than Kogge-Stone
- **~40% fewer cells** than Kogge-Stone for same width
- **Constant fanout of 2** - Better for advanced process nodes
- **Reduced wiring** - 4 tracks vs 8 for Kogge-Stone (16-bit)
- **Optimal for** multiplier final CPA and FMA wide addition

## Module Hierarchy

**Top-Level Modules:**
- `math_adder_han_carlson_016.sv` - 16-bit adder (for BF16 multiplier CPA)
- `math_adder_han_carlson_048.sv` - 48-bit adder (for BF16 FMA wide addition)

**Building Blocks:**
- `math_prefix_cell.sv` - Black cell (outputs G and P)
- `math_prefix_cell_gray.sv` - Gray cell (outputs G only)

## Module Declaration

### 16-bit Han-Carlson Adder

```systemverilog
module math_adder_han_carlson_016 #(
    parameter int N = 16
) (
    input  logic [N-1:0] i_a,
    input  logic [N-1:0] i_b,
    input  logic         i_cin,
    output logic [N-1:0] ow_sum,
    output logic         ow_cout
);
```

### 48-bit Han-Carlson Adder

```systemverilog
module math_adder_han_carlson_048 #(
    parameter int N = 48
) (
    input  logic [N-1:0] i_a,
    input  logic [N-1:0] i_b,
    input  logic         i_cin,
    output logic [N-1:0] ow_sum,
    output logic         ow_cout
);
```

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N | int | 16/48 | Adder width (fixed per variant) |

**Note:** The N parameter is fixed per module variant. Use the appropriate variant for your width.

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_a | Input | N | First operand |
| i_b | Input | N | Second operand |
| i_cin | Input | 1 | Carry input |
| ow_sum | Output | N | Sum result (A + B + Cin) |
| ow_cout | Output | 1 | Carry output |

## Algorithm

### Han-Carlson Structure

Han-Carlson uses a "sparsity-2" approach:

1. **Stage 0:** Compute initial P and G for all positions
2. **Stage 1:** Combine adjacent pairs on even positions only
3. **Stages 2-N:** Kogge-Stone style prefix on even positions (doubling span)
4. **Final Stage:** Fill odd positions from even neighbors using gray cells

### Stage-by-Stage Breakdown (16-bit)

```
Stage 0: Initial P/G computation
  P[i] = A[i] XOR B[i]
  G[i] = A[i] AND B[i]

Stage 1: Span-2 prefix on even positions
  Position 0: G[0:-1] (incorporate cin)
  Even positions: G[i:i-1] = combine(G[i], P[i], G[i-1], P[i-1])
  Odd positions: pass through

Stage 2: Span-4 prefix on even positions (step 2)
  Even positions >= 2: G[i:i-3] = combine(G[i:i-1], G[i-2:i-3])
  Others: pass through

Stage 3: Span-8 prefix on even positions (step 4)
  Even positions >= 4: G[i:i-7] = combine(G[i:i-3], G[i-4:i-7])
  Others: pass through

Stage 4: Span-16 prefix on even positions (step 8)
  Even positions >= 8: G[i:i-15] = combine(...)
  Others: pass through

Stage 5: Fill odd positions (gray cells)
  Odd positions: G[i:-1] = combine(G[i], P[i], G[i-1:-1])
  Even positions: pass through

Sum computation:
  Sum[0] = P[0] XOR Cin
  Sum[i] = P[i] XOR G[i-1:-1]
```

### Prefix Network Visualization (16-bit simplified)

```
Position:   0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  15

Stage 0:    o   o   o   o   o   o   o   o   o   o   o   o   o   o   o   o
            Initial P/G generation

Stage 1:    *   |   *   |   *   |   *   |   *   |   *   |   *   |   *   |
            Even positions combine with odd neighbor (*)
            Odd positions pass through (|)

Stage 2:    *   |   |   |   *   |   |   |   *   |   |   |   *   |   |   |
            Even positions combine with step=2 (positions 2,4,6,8,10,12,14)

Stage 3:    *   |   |   |   |   |   |   |   *   |   |   |   |   |   |   |
            Even positions combine with step=4 (positions 4,8,12)

Stage 4:    *   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |
            Even positions combine with step=8 (positions 8)

Stage 5:    o   *   o   *   o   *   o   *   o   *   o   *   o   *   o   *
            Fill odd positions with gray cells (*)

Legend: o=pass through, |=pass through, *=prefix cell
```

### Why Han-Carlson is Optimal

| Metric | Kogge-Stone | Brent-Kung | Han-Carlson |
|--------|-------------|------------|-------------|
| Logic Depth (16-bit) | 4 | 7 | 5 |
| Prefix Cells (16-bit) | 64 | ~30 | ~39 |
| Wiring Tracks | 8 | 2 | 4 |
| Fanout | Varies | 2 | 2 |
| Best For | Max speed | Min area | Balanced |

**Han-Carlson achieves:**
- 1 level slower than Kogge-Stone (5 vs 4)
- 40% fewer cells than Kogge-Stone (39 vs 64)
- 2x fewer wiring tracks than Kogge-Stone (4 vs 8)
- Constant fanout of 2 (important for advanced nodes)

## Timing Characteristics

### 16-bit Adder

| Metric | Value |
|--------|-------|
| Logic Levels | 5 stages + sum XOR |
| Prefix Cells | ~39 (black + gray) |
| Critical Path | cin -> Stage 1 -> Stage 5 -> sum[15] |

### 48-bit Adder

| Metric | Value |
|--------|-------|
| Logic Levels | 7 stages + sum XOR |
| Prefix Cells | ~120 (black + gray) |
| Critical Path | cin -> Stage 1 -> Stage 7 -> sum[47] |

### Depth Formula

For N-bit Han-Carlson:
- **Depth** = ceil(log2(N)) + 2 stages
- **16-bit:** ceil(log2(16)) + 2 = 4 + 2 = 6 stages (5 prefix + 1 sum)
- **48-bit:** ceil(log2(48)) + 2 = 6 + 2 = 8 stages (7 prefix + 1 sum)

## Usage Examples

### Basic 16-bit Addition

```systemverilog
logic [15:0] a, b, sum;
logic cout;

math_adder_han_carlson_016 u_add (
    .i_a(a),
    .i_b(b),
    .i_cin(1'b0),
    .ow_sum(sum),
    .ow_cout(cout)
);
```

### Subtraction (A - B)

```systemverilog
logic [15:0] a, b, diff;
logic borrow;

// A - B = A + (~B) + 1
math_adder_han_carlson_016 u_sub (
    .i_a(a),
    .i_b(~b),
    .i_cin(1'b1),  // +1 for two's complement
    .ow_sum(diff),
    .ow_cout(borrow)
);
```

### In BF16 Multiplier (Final CPA)

```systemverilog
// Final carry-propagate addition after Dadda reduction
wire [15:0] w_cpa_a, w_cpa_b;  // From Dadda tree
wire [15:0] w_product;
wire        w_cout;

math_adder_han_carlson_016 u_final_cpa (
    .i_a(w_cpa_a),
    .i_b(w_cpa_b),
    .i_cin(1'b0),
    .ow_sum(w_product),
    .ow_cout(w_cout)  // Unused for unsigned multiply
);
```

### In BF16 FMA (Wide Addition)

```systemverilog
// 48-bit mantissa addition in FMA
wire [47:0] w_mant_larger, w_mant_smaller_aligned;
wire [47:0] w_sum;
wire        w_cout;

// For subtraction, invert smaller operand
wire [47:0] w_adder_b = w_effective_sub ? ~w_mant_smaller_aligned
                                        : w_mant_smaller_aligned;

math_adder_han_carlson_048 u_wide_add (
    .i_a(w_mant_larger),
    .i_b(w_adder_b),
    .i_cin(w_effective_sub),  // +1 for two's complement
    .ow_sum(w_sum),
    .ow_cout(w_cout)
);
```

## Performance Characteristics

### Resource Utilization

| Width | Black Cells | Gray Cells | Total Cells | LUTs (Est.) |
|-------|-------------|------------|-------------|-------------|
| 16-bit | ~31 | 8 | ~39 | ~80 |
| 48-bit | ~96 | 24 | ~120 | ~250 |

### Comparison with Other Architectures

| Architecture | 16-bit Depth | 16-bit Cells | Wiring Complexity |
|--------------|--------------|--------------|-------------------|
| Ripple Carry | 16 | 16 | Minimal |
| Brent-Kung | 7 | ~30 | Low |
| **Han-Carlson** | **5** | **~39** | **Medium** |
| Kogge-Stone | 4 | 64 | High |

## Design Considerations

### Design Optimization Priorities

This module is optimized with the following priorities:
1. **Area** - Fewer cells than Kogge-Stone via sparsity-2 structure
2. **Wire complexity** - Reduced wiring tracks and constant fanout
3. **Logic depth** - Near-optimal O(log N + 1) depth

### When to Use Han-Carlson

**Appropriate Use Cases:**
- Multiplier final CPA (balanced speed/area)
- FMA wide addition (48+ bits)
- Designs targeting advanced process nodes where wire delay matters
- Area-constrained high-speed arithmetic

**Consider Alternatives When:**
- Absolute minimum depth needed -> Kogge-Stone
- Absolute minimum area needed -> Brent-Kung or Ripple Carry
- Width not power-of-2 -> Consider behavioral or Ripple Carry

### Auto-Generated Code

These modules are auto-generated by Python scripts:
- **Generator:** `bin/rtl_generators/bf16/han_carlson_adder.py`
- **Regenerate:** `PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/generate_all.py rtl/common`

**Do not edit the generated .sv files manually.** Modify the generator script instead.

## Common Pitfalls

**Anti-Pattern 1:** Expecting parameterizable width
```systemverilog
// WRONG: N is fixed per variant
math_adder_han_carlson_016 #(.N(24)) u_add (...);  // Won't work!

// RIGHT: Use appropriate variant or extend inputs
math_adder_han_carlson_048 u_add (
    .i_a({24'b0, a[23:0]}),  // Zero-extend
    .i_b({24'b0, b[23:0]}),
    ...
);
```

**Anti-Pattern 2:** Ignoring that outputs are combinational
```systemverilog
// Remember: outputs are purely combinational
// Add pipeline registers if needed for timing closure
always_ff @(posedge clk) begin
    sum_reg <= ow_sum;  // Register the output
end
```

## Related Modules

- **math_prefix_cell** - Black cell building block
- **math_prefix_cell_gray** - Gray cell building block
- **math_multiplier_dadda_4to2_008** - Uses 16-bit Han-Carlson for final CPA
- **math_bf16_fma** - Uses 48-bit Han-Carlson for wide addition
- **math_adder_brent_kung_nbit** - Alternative area-optimized adder
- **math_adder_kogge_stone_nbit** - Maximum speed alternative

## References

- Han, T., Carlson, D.A. "Fast Area-Efficient VLSI Adders." IEEE Symposium on Computer Arithmetic, 1987.
- Harris, D. "A Taxonomy of Parallel Prefix Networks." Asilomar Conference, 2003.
- Knowles, S. "A Family of Adders." IEEE Symposium on Computer Arithmetic, 1999.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
