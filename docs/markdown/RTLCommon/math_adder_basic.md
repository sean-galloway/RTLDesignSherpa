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

# Basic Adder Building Blocks

Fundamental single-bit and multi-bit adder primitives (half adder, full adder, and N-bit full adder array) that serve as building blocks for more complex arithmetic circuits.

## Overview

This document covers the three basic adder modules that form the foundation of all adder architectures:
- **math_adder_half** - Single-bit half adder (2 inputs: A, B)
- **math_adder_full** - Single-bit full adder (3 inputs: A, B, Cin)
- **math_adder_full_nbit** - N-bit array of full adders (identical to ripple carry adder)

These modules are used as building blocks in ripple carry adders, carry-save adders, multipliers, and other arithmetic circuits.

## Module Declarations

### Half Adder

```systemverilog
module math_adder_half #(
    parameter int N = 1      // Unused parameter (kept for consistency)
) (
    input  logic i_a,        // Input A
    input  logic i_b,        // Input B
    output logic ow_sum,     // Sum output
    output logic ow_carry    // Carry output
);
```

### Full Adder

```systemverilog
module math_adder_full #(
    parameter int N = 1      // Unused parameter (kept for consistency)
) (
    input  logic i_a,        // Input A
    input  logic i_b,        // Input B
    input  logic i_c,        // Carry input
    output logic ow_sum,     // Sum output
    output logic ow_carry    // Carry output
);
```

### N-bit Full Adder Array

```systemverilog
module math_adder_full_nbit #(
    parameter int N = 4      // Number of bits
) (
    input  logic [N-1:0] i_a,       // Operand A
    input  logic [N-1:0] i_b,       // Operand B
    input  logic         i_c,       // Initial carry input
    output logic [N-1:0] ow_sum,    // Sum output
    output logic         ow_carry   // Final carry output
);
```

## Parameters

### Half Adder & Full Adder

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N | int | 1 | Unused legacy parameter (single-bit modules) |

**Note:** The `N` parameter exists for consistency but is not used. These are single-bit modules.

### N-bit Full Adder Array

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N | int | 4 | Number of bits in the adder (range: 1-64) |

## Ports

### Half Adder Ports

| Port | Width | Description |
|------|-------|-------------|
| i_a | 1 | Input A |
| i_b | 1 | Input B |
| ow_sum | 1 | Sum output (A ^ B) |
| ow_carry | 1 | Carry output (A & B) |

### Full Adder Ports

| Port | Width | Description |
|------|-------|-------------|
| i_a | 1 | Input A |
| i_b | 1 | Input B |
| i_c | 1 | Carry input |
| ow_sum | 1 | Sum output (A ^ B ^ Cin) |
| ow_carry | 1 | Carry output |

### N-bit Full Adder Ports

| Port | Width | Description |
|------|-------|-------------|
| i_a | N | Operand A |
| i_b | N | Operand B |
| i_c | 1 | Initial carry input |
| ow_sum | N | Sum output (A + B + Cin) |
| ow_carry | 1 | Final carry output |

## Functionality

### Half Adder

The half adder adds two single-bit inputs without carry input:

**Logic Equations:**
```
Sum = A ⊕ B     (XOR)
Carry = A • B   (AND)
```

**Truth Table:**
| A | B | Sum | Carry |
|---|---|-----|-------|
| 0 | 0 | 0   | 0     |
| 0 | 1 | 1   | 0     |
| 1 | 0 | 1   | 0     |
| 1 | 1 | 0   | 1     |

**Implementation:**
```systemverilog
assign ow_sum   = i_a ^ i_b;    // XOR for sum
assign ow_carry = i_a & i_b;    // AND for carry
```

**Use Cases:**
- LSB addition when no carry input exists
- Building block for full adders
- Parity generation (sum output)
- Detecting when both inputs are 1 (carry output)

### Full Adder

The full adder adds three single-bit inputs (A, B, Cin):

**Logic Equations:**
```
Sum = A ⊕ B ⊕ Cin
Carry = (A • B) | (Cin • (A ⊕ B))
      = Majority(A, B, Cin)
```

**Truth Table:**
| A | B | Cin | Sum | Cout |
|---|---|-----|-----|------|
| 0 | 0 | 0   | 0   | 0    |
| 0 | 0 | 1   | 1   | 0    |
| 0 | 1 | 0   | 1   | 0    |
| 0 | 1 | 1   | 0   | 1    |
| 1 | 0 | 0   | 1   | 0    |
| 1 | 0 | 1   | 0   | 1    |
| 1 | 1 | 0   | 0   | 1    |
| 1 | 1 | 1   | 1   | 1    |

**Implementation:**
```systemverilog
assign ow_sum   = i_a ^ i_b ^ i_c;              // 3-input XOR
assign ow_carry = (i_a & i_b) | (i_c & (i_a ^ i_b));  // Majority function
```

**Alternative Carry Implementation (equivalent):**
```systemverilog
assign ow_carry = (i_a & i_b) | (i_a & i_c) | (i_b & i_c);  // Full majority
```

**Use Cases:**
- Building block for ripple carry adders
- Building block for carry-save adders
- Multi-bit addition (chained together)
- 3:2 compression in multiplier trees

### N-bit Full Adder Array

Chains N full adders to create a multi-bit adder:

**Structure:**
```
Bit 0:   FA(A[0], B[0], Cin)     → Sum[0], C[0]
Bit 1:   FA(A[1], B[1], C[0])    → Sum[1], C[1]
Bit 2:   FA(A[2], B[2], C[1])    → Sum[2], C[2]
...
Bit N-1: FA(A[N-1], B[N-1], C[N-2]) → Sum[N-1], Cout
```

**Implementation:**
```systemverilog
logic [N:0] w_c;  // Intermediate carries
assign w_c[0] = i_c;  // Initial carry

genvar i;
generate
    for (i = 0; i < N; i++) begin : gen_full_adders
        math_adder_full fa (
            .i_a(i_a[i]),
            .i_b(i_b[i]),
            .i_c(w_c[i]),
            .ow_sum(ow_sum[i]),
            .ow_carry(w_c[i+1])
        );
    end
endgenerate

assign ow_carry = w_c[N];  // Final carry out
```

**Note:** This module is functionally identical to `math_adder_ripple_carry`. The only difference is internal structure:
- `math_adder_ripple_carry`: Instantiates first FA separately, then generates remaining
- `math_adder_full_nbit`: Uniform generate loop for all FAs

## Usage Examples

### Half Adder: Parity Generator

```systemverilog
logic [7:0] data;
logic parity;

// Generate even parity bit
genvar i;
generate
    if (i == 0) begin
        assign parity_chain[0] = data[0];
    end else begin
        math_adder_half u_parity (
            .i_a(data[i]),
            .i_b(parity_chain[i-1]),
            .ow_sum(parity_chain[i]),  // XOR accumulation
            .ow_carry()                 // Unused
        );
    end
endgenerate

assign parity = parity_chain[7];
```

### Full Adder: Carry-Save Adder Stage

```systemverilog
// Add 3 numbers using carry-save adder (1 level)
logic [7:0] a, b, c;
logic [7:0] sum, carry;

genvar i;
generate
    for (i = 0; i < 8; i++) begin : gen_csa
        math_adder_full fa (
            .i_a(a[i]),
            .i_b(b[i]),
            .i_c(c[i]),
            .ow_sum(sum[i]),      // Sum bits
            .ow_carry(carry[i])   // Carry bits (shifted left)
        );
    end
endgenerate

// Final result: sum + (carry << 1) using conventional adder
logic [8:0] result;
assign result = {1'b0, sum} + {carry, 1'b0};
```

### N-bit Full Adder: BCD Digit Adder

```systemverilog
// Add two BCD digits (0-9)
logic [3:0] bcd_a, bcd_b, bcd_sum_raw;
logic carry_raw;

math_adder_full_nbit #(.N(4)) u_bcd_add (
    .i_a(bcd_a),
    .i_b(bcd_b),
    .i_c(1'b0),
    .ow_sum(bcd_sum_raw),
    .ow_carry(carry_raw)
);

// BCD correction
logic bcd_overflow;
assign bcd_overflow = carry_raw | (bcd_sum_raw > 4'd9);

logic [3:0] bcd_sum_corrected;
math_adder_full_nbit #(.N(4)) u_bcd_correct (
    .i_a(bcd_sum_raw),
    .i_b(bcd_overflow ? 4'd6 : 4'd0),  // Add 6 for correction
    .i_c(1'b0),
    .ow_sum(bcd_sum_corrected),
    .ow_carry()
);
```

### Building a 2-bit Adder from Scratch

```systemverilog
logic [1:0] a, b, sum;
logic cin, cout;
logic c_intermediate;

// Bit 0: Half adder (if no carry input) or full adder
math_adder_full fa0 (
    .i_a(a[0]),
    .i_b(b[0]),
    .i_c(cin),
    .ow_sum(sum[0]),
    .ow_carry(c_intermediate)
);

// Bit 1: Full adder
math_adder_full fa1 (
    .i_a(a[1]),
    .i_b(b[1]),
    .i_c(c_intermediate),
    .ow_sum(sum[1]),
    .ow_carry(cout)
);
```

## Timing Characteristics

### Propagation Delays

| Module | Logic Levels | Typical Delay (ns) |
|--------|--------------|-------------------|
| Half Adder | 1 (XOR/AND parallel) | ~0.2 |
| Full Adder | 2 (XOR then carry) | ~0.4 |
| N-bit Array | 2N (ripple chain) | ~0.4N |

**Critical Paths:**

**Half Adder:**
```
i_a/i_b → ow_sum    (1 XOR gate)
i_a/i_b → ow_carry  (1 AND gate)
```

**Full Adder:**
```
i_a/i_b/i_c → ow_sum    (2 XOR gates)
i_a/i_b/i_c → ow_carry  (2 gates: XOR + OR/AND)
```

**N-bit Array:**
```
i_c → FA[0].Cout → FA[1].Cout → ... → FA[N-1].Cout → ow_carry
     (2N gate delays)
```

## Performance Characteristics

### Resource Utilization

| Module | LUTs | Description |
|--------|------|-------------|
| Half Adder | 2 | 1 XOR + 1 AND |
| Full Adder | 2 | Optimized to 2 LUTs on modern FPGAs |
| N-bit Array | ~2N | N full adders |

**FPGA Note:** Modern FPGAs (Xilinx, Intel) have dedicated carry chain logic that implements full adders very efficiently, often faster than generic LUT logic.

### When to Use Each Module

**Half Adder:**
- ✅ First bit of addition chain (no carry input)
- ✅ Parity generation
- ✅ Educational/demonstration purposes
- ❌ Rarely used standalone in production designs

**Full Adder:**
- ✅ Building block for custom arithmetic circuits
- ✅ Carry-save adder stages
- ✅ Multiplier partial product reduction
- ✅ When instantiating adder arrays manually

**N-bit Array:**
- ✅ Quick multi-bit adder for small widths (N ≤ 8)
- ✅ When ripple carry is acceptable
- ❌ For N > 8, consider carry lookahead or parallel prefix

## Design Considerations

### Why Use These Modules

**Advantages:**
- **Minimal area**: Absolute smallest implementation
- **Simple**: Easy to understand and verify
- **Building blocks**: Compose into larger structures
- **FPGA-friendly**: Maps well to carry chain primitives

**Disadvantages:**
- **Slow for wide widths**: O(N) delay
- **Not optimal**: Synthesis tools can often do better
- **Manual instantiation**: More code than behavioral `+` operator

### Behavioral vs Structural

**Behavioral (Let synthesis infer):**
```systemverilog
// Simple, synthesis tool optimizes
assign sum = a + b + cin;
```

**Structural (Explicit full adders):**
```systemverilog
// Manual control, educational
genvar i;
generate
    for (i = 0; i < N; i++) begin
        math_adder_full fa (...);
    end
endgenerate
```

**Recommendation:** Use behavioral unless you need explicit control (e.g., carry-save adders, multipliers, custom timing control).

### FPGA-Specific Considerations

Modern FPGAs have dedicated adder resources:
- **Xilinx**: CARRY4 primitives
- **Intel**: Carry chain logic
- **Result**: Behavioral `+` often as fast as manual instantiation

**Exception:** Carry-save adders and multiplier trees benefit from explicit full adder instantiation.

## Common Pitfalls

❌ **Anti-Pattern 1**: Using half adder where full adder needed

```systemverilog
// WRONG: Half adder can't accept carry input
math_adder_half fa0 (
    .i_a(a[0]), .i_b(b[0]),
    .i_c(cin),  // ERROR: No i_c port!
    ...
);

// RIGHT: Use full adder
math_adder_full fa0 (
    .i_a(a[0]), .i_b(b[0]), .i_c(cin), ...
);
```

❌ **Anti-Pattern 2**: Over-engineering simple additions

```systemverilog
// WRONG: Manual full adder chain for simple addition
// (More code, no benefit)
genvar i;
generate
    for (i = 0; i < 16; i++) begin
        math_adder_full fa (...);
    end
endgenerate

// RIGHT: Use behavioral code (simpler, tool optimizes)
assign sum = a + b;
```

❌ **Anti-Pattern 3**: Ignoring synthesis capabilities

```systemverilog
// Behavioral code synthesizes to optimal adder anyway:
assign sum = a + b;

// No need for explicit full adders unless:
// - Building carry-save adder
// - Building multiplier tree
// - Educational/demonstration purpose
```

❌ **Anti-Pattern 4**: Incorrect carry chain connection

```systemverilog
// WRONG: Carry not properly chained
math_adder_full fa0 (..., .ow_carry(c[0]));
math_adder_full fa1 (..., .i_c(c[0]));  // Missing intermediate connection

// RIGHT: Ensure proper carry propagation
math_adder_full fa0 (..., .ow_carry(w_c[0]));
math_adder_full fa1 (..., .i_c(w_c[0]), .ow_carry(w_c[1]));
```

## Related Modules

- **math_adder_ripple_carry.sv** - Uses full adders for N-bit addition
- **math_adder_carry_save.sv** - Parallel full adders (no carry chain)
- **math_multiplier_*.sv** - Uses full adders for partial product reduction
- **math_adder_full_nbit.sv** - Identical functionality to ripple carry adder

## References

- Mano, M.M. "Digital Design." Prentice Hall, 2002.
- Wakerly, J.F. "Digital Design: Principles and Practices." Pearson, 2006.
- Hennessy, J.L., Patterson, D.A. "Computer Architecture: A Quantitative Approach." Morgan Kaufmann, 2011.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
