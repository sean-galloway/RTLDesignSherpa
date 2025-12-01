# Prefix Cell (Black Cell)

A parallel prefix network building block that combines generate (G) and propagate (P) signals from adjacent bit groups, used in high-performance adders like Kogge-Stone, Brent-Kung, and Han-Carlson.

## Overview

The `math_prefix_cell` module (also known as a "black cell") implements the fundamental prefix operation for parallel prefix adders. It combines the generate and propagate signals from a higher bit position with those from a lower bit position, computing the group generate and group propagate for the combined range.

**Key Features:**
- **Outputs both G and P** - Full prefix cell for forward tree stages
- **O(1) delay** - Fixed 2-gate delay per stage
- **Building block** for all parallel prefix adder architectures
- **Enables O(log N) addition** - Parallel carry computation

## Module Declaration

```systemverilog
module math_prefix_cell (
    input  logic i_g_hi, i_p_hi,   // From higher bit position
    input  logic i_g_lo, i_p_lo,   // From lower bit position
    output logic ow_g, ow_p
);
```

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_g_hi | Input | 1 | Generate signal from higher bit position [i:k] |
| i_p_hi | Input | 1 | Propagate signal from higher bit position [i:k] |
| i_g_lo | Input | 1 | Generate signal from lower bit position [k-1:j] |
| i_p_lo | Input | 1 | Propagate signal from lower bit position [k-1:j] |
| ow_g | Output | 1 | Combined group generate [i:j] |
| ow_p | Output | 1 | Combined group propagate [i:j] |

## Functionality

### Parallel Prefix Theory

In parallel prefix adders, carries are computed using generate (G) and propagate (P) signals:

**Bit-level definitions:**
- **Generate:** G[i] = A[i] AND B[i] - Carry generated at position i
- **Propagate:** P[i] = A[i] XOR B[i] - Carry propagated through position i

**Group-level recurrence (the prefix operation):**
- **G[i:j]** = G[i:k] OR (P[i:k] AND G[k-1:j])
- **P[i:j]** = P[i:k] AND P[k-1:j]

This cell computes these group-level signals by combining two adjacent ranges.

### Implementation

```systemverilog
assign ow_g = i_g_hi | (i_p_hi & i_g_lo);
assign ow_p = i_p_hi & i_p_lo;
```

**Interpretation:**
- **Group Generate:** A carry is generated for the combined range if:
  - The high range generates a carry, OR
  - The high range propagates AND the low range generates
- **Group Propagate:** A carry propagates through the combined range only if both ranges propagate

### Example: Combining Adjacent Pairs

```
Initial (bit-level):
  Position:  3    2    1    0
  P[i]:     P3   P2   P1   P0
  G[i]:     G3   G2   G1   G0

After Stage 1 (prefix cells combining adjacent pairs):
  G[1:0] = G1 | (P1 & G0)     // Does range [1:0] generate?
  P[1:0] = P1 & P0            // Does range [1:0] propagate?

  G[3:2] = G3 | (P3 & G2)     // Does range [3:2] generate?
  P[3:2] = P3 & P2            // Does range [3:2] propagate?

After Stage 2 (prefix cells combining pairs of pairs):
  G[3:0] = G[3:2] | (P[3:2] & G[1:0])  // Does range [3:0] generate?
  P[3:0] = P[3:2] & P[1:0]             // Does range [3:0] propagate?
```

## Timing Characteristics

| Metric | Value | Description |
|--------|-------|-------------|
| Logic Depth | 2 gates | 1 AND + 1 OR (for G), 1 AND (for P) |
| Critical Path | AND-OR | i_g_hi/i_p_hi -> ow_g |
| Gate Count | 3 | 2 AND gates + 1 OR gate |

## Usage Examples

### In Kogge-Stone Adder (Stage 1)

```systemverilog
// Combine positions 1 and 0
math_prefix_cell u_pf_10 (
    .i_g_hi(g[1]),   .i_p_hi(p[1]),
    .i_g_lo(g[0]),   .i_p_lo(p[0]),
    .ow_g(g_1_0),    .ow_p(p_1_0)
);

// Combine positions 3 and 2
math_prefix_cell u_pf_32 (
    .i_g_hi(g[3]),   .i_p_hi(p[3]),
    .i_g_lo(g[2]),   .i_p_lo(p[2]),
    .ow_g(g_3_2),    .ow_p(p_3_2)
);
```

### In Kogge-Stone Adder (Stage 2)

```systemverilog
// Combine ranges [3:2] and [1:0]
math_prefix_cell u_pf_30 (
    .i_g_hi(g_3_2),  .i_p_hi(p_3_2),
    .i_g_lo(g_1_0),  .i_p_lo(p_1_0),
    .ow_g(g_3_0),    .ow_p(p_3_0)
);
```

### In Han-Carlson Adder (Even Position)

```systemverilog
// Han-Carlson: Only even positions get prefix cells in intermediate stages
generate
    for (i = 0; i < N; i++) begin : gen_stage
        if (i % 2 == 0 && i >= 2) begin : gen_even
            math_prefix_cell u_pf (
                .i_g_hi(w_g_prev[i]),   .i_p_hi(w_p_prev[i]),
                .i_g_lo(w_g_prev[i-2]), .i_p_lo(w_p_prev[i-2]),
                .ow_g(w_g_curr[i]),     .ow_p(w_p_curr[i])
            );
        end else begin : gen_pass
            assign w_g_curr[i] = w_g_prev[i];
            assign w_p_curr[i] = w_p_prev[i];
        end
    end
endgenerate
```

## Performance Characteristics

### Resource Utilization

| Metric | Value |
|--------|-------|
| AND gates | 2 |
| OR gates | 1 |
| Total gates | 3 |
| LUTs (FPGA) | 1-2 |

### Comparison: Black Cell vs Gray Cell

| Property | Black Cell (this) | Gray Cell |
|----------|-------------------|-----------|
| Outputs | G and P | G only |
| Gate count | 3 | 2 |
| Use case | Forward tree | Reverse tree / final stage |
| Module | `math_prefix_cell` | `math_prefix_cell_gray` |

## Design Considerations

### When to Use Black vs Gray Cells

**Use Black Cells (this module) when:**
- In forward tree stages where both G and P are needed downstream
- Building Kogge-Stone style networks (all cells are black)
- Intermediate stages of Brent-Kung or Han-Carlson

**Use Gray Cells when:**
- Only the carry (G) is needed (final sum computation)
- In reverse tree stages of Brent-Kung
- Final fill-in stage of Han-Carlson
- ~33% area savings when P not needed

### Design Optimization Priorities

This module is optimized with the following priorities:
1. **Area** - Minimal 3-gate implementation
2. **Wire complexity** - Simple point-to-point connections
3. **Logic depth** - Fixed 2-gate delay

### Prefix Network Architectures

| Architecture | Black Cells | Gray Cells | Depth | Wiring |
|--------------|-------------|------------|-------|--------|
| Kogge-Stone | All | None | O(log N) | Maximum |
| Brent-Kung | Forward tree | Reverse tree | O(2 log N) | Minimum |
| Han-Carlson | Even positions | Final stage | O(log N + 1) | Medium |

## Related Modules

- **math_prefix_cell_gray** - Gray cell variant (G output only)
- **math_adder_han_carlson_016** - 16-bit Han-Carlson adder using this cell
- **math_adder_han_carlson_048** - 48-bit Han-Carlson adder using this cell
- **math_adder_brent_kung_black** - Brent-Kung black cell (equivalent)
- **math_adder_kogge_stone_nbit** - Kogge-Stone adder using black cells

## Applications

- **High-performance adders** - All parallel prefix adder architectures
- **Multiplier final CPA** - Fast carry-propagate addition
- **Incrementers/Decrementers** - Priority-encoded operations
- **Comparators** - Parallel comparison networks

## References

- Kogge, P.M., Stone, H.S. "A Parallel Algorithm for the Efficient Solution of a General Class of Recurrence Equations." IEEE Trans. Computers, 1973.
- Brent, R.P., Kung, H.T. "A Regular Layout for Parallel Adders." IEEE Trans. Computers, 1982.
- Han, T., Carlson, D.A. "Fast Area-Efficient VLSI Adders." IEEE Symposium on Computer Arithmetic, 1987.
- Harris, D. "A Taxonomy of Parallel Prefix Networks." Asilomar Conference, 2003.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
