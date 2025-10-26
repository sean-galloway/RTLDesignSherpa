# Binary Subtractors

A family of binary subtractor modules (half, full, ripple, and carry lookahead) for computing A - B using direct subtraction logic. Modern designs typically use adders with two's complement instead, but these modules are useful for educational purposes and specific applications.

## Overview

This document covers the complete subtractor module family:
- **math_subtractor_half** - Single-bit half subtractor (2 inputs)
- **math_subtractor_full** - Single-bit full subtractor (3 inputs with borrow)
- **math_subtractor_full_nbit** - N-bit ripple borrow subtractor
- **math_subtractor_ripple_carry** - N-bit ripple borrow subtractor (equivalent)
- **math_subtractor_carry_lookahead** - N-bit subtractor with lookahead logic

**Modern Alternative:** Most designs use adders for subtraction via two's complement: `A - B = A + (~B) + 1`. This approach reuses existing adder hardware.

## Module Declarations

### Half Subtractor

```systemverilog
module math_subtractor_half (
    input  logic i_a,       // Minuend
    input  logic i_b,       // Subtrahend
    output logic o_d,       // Difference
    output logic o_b        // Borrow output
);
```

### Full Subtractor

```systemverilog
module math_subtractor_full (
    input  logic i_a,       // Minuend
    input  logic i_b,       // Subtrahend
    input  logic i_b_in,    // Borrow input
    output logic ow_d,      // Difference
    output logic ow_b       // Borrow output
);
```

### N-bit Ripple Borrow Subtractor

```systemverilog
module math_subtractor_ripple_carry #(
    parameter int N = 4
) (
    input  logic [N-1:0] i_a,       // Minuend
    input  logic [N-1:0] i_b,       // Subtrahend
    input  logic         i_b_in,    // Borrow input
    output logic [N-1:0] ow_d,      // Difference
    output logic         ow_b       // Borrow output
);
```

### N-bit Carry Lookahead Subtractor

```systemverilog
module math_subtractor_carry_lookahead #(
    parameter int N = 4
) (
    input  logic [N-1:0] i_a,       // Minuend
    input  logic [N-1:0] i_b,       // Subtrahend
    input  logic         i_b_in,    // Borrow input
    output logic [N-1:0] ow_d,      // Difference
    output logic         ow_b       // Borrow output
);
```

## Parameters

### Single-bit Subtractors

No parameters (fixed single-bit operation).

### N-bit Subtractors

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N | int | 4 | Bit width (range: 1-64) |

## Ports

### Half Subtractor Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_a | Input | 1 | Minuend (number to subtract from) |
| i_b | Input | 1 | Subtrahend (number to subtract) |
| o_d | Output | 1 | Difference output (A - B) |
| o_b | Output | 1 | Borrow output |

### Full Subtractor Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_a | Input | 1 | Minuend |
| i_b | Input | 1 | Subtrahend |
| i_b_in | Input | 1 | Borrow input (from previous stage) |
| ow_d | Output | 1 | Difference output |
| ow_b | Output | 1 | Borrow output (to next stage) |

### N-bit Subtractor Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_a | Input | N | Minuend vector |
| i_b | Input | N | Subtrahend vector |
| i_b_in | Input | 1 | Initial borrow input |
| ow_d | Output | N | Difference vector (A - B - Bin) |
| ow_b | Output | 1 | Final borrow output |

## Functionality

### Half Subtractor

Subtracts one bit from another without borrow input:

**Logic Equations:**
```
Difference = A ⊕ B             // XOR
Borrow = ~A • B                // Borrow when A=0, B=1
```

**Truth Table:**
| A | B | Diff | Borrow | Meaning |
|---|---|------|--------|---------|
| 0 | 0 | 0    | 0      | 0 - 0 = 0 |
| 0 | 1 | 1    | 1      | 0 - 1 = -1 (borrow!) |
| 1 | 0 | 1    | 0      | 1 - 0 = 1 |
| 1 | 1 | 0    | 0      | 1 - 1 = 0 |

**Implementation:**
```systemverilog
assign o_d = i_a ^ i_b;         // XOR for difference
assign o_b = ~i_a & i_b;        // Borrow when A < B
```

### Full Subtractor

Subtracts two bits with borrow input:

**Logic Equations:**
```
Difference = A ⊕ B ⊕ Bin
Borrow = (~A • B) | (~(A ⊕ B) • Bin)
       = (~A • B) | (~A • Bin) | (B • Bin)  // Alternative form
```

**Truth Table:**
| A | B | Bin | Diff | Bout | A - B - Bin |
|---|---|-----|------|------|-------------|
| 0 | 0 | 0   | 0    | 0    | 0           |
| 0 | 0 | 1   | 1    | 1    | -1          |
| 0 | 1 | 0   | 1    | 1    | -1          |
| 0 | 1 | 1   | 0    | 1    | -2          |
| 1 | 0 | 0   | 1    | 0    | 1           |
| 1 | 0 | 1   | 0    | 0    | 0           |
| 1 | 1 | 0   | 0    | 0    | 0           |
| 1 | 1 | 1   | 1    | 1    | -1          |

**Implementation:**
```systemverilog
assign ow_d = i_a ^ i_b ^ i_b_in;
assign ow_b = (~i_a & i_b) | (~(i_a ^ i_b) & i_b_in);
```

### N-bit Ripple Borrow Subtractor

Chains N full subtractors with borrow propagating from LSB to MSB:

```
Bit 0:   FS(A[0], B[0], Bin)     → D[0], B[0]
Bit 1:   FS(A[1], B[1], B[0])    → D[1], B[1]
...
Bit N-1: FS(A[N-1], B[N-1], B[N-2]) → D[N-1], Bout
```

**Timing:** O(N) delay (borrow ripples sequentially)

### N-bit Carry Lookahead Subtractor

Uses lookahead logic to compute borrows faster (similar to CLA adder):

**Timing:** O(N) delay (simplified lookahead)

## Usage Examples

### Basic Subtraction (Using Subtractor)

```systemverilog
logic [7:0] a, b, diff;
logic borrow;

math_subtractor_ripple_carry #(.N(8)) u_sub (
    .i_a(a),
    .i_b(b),
    .i_b_in(1'b0),      // No initial borrow
    .ow_d(diff),
    .ow_b(borrow)       // Borrow indicates A < B
);

// Example: 100 - 50 = 50
initial begin
    a = 8'd100;
    b = 8'd50;
    #1;
    assert(diff == 8'd50);
    assert(borrow == 1'b0);  // No borrow
end
```

### Detecting Underflow (A < B)

```systemverilog
logic [7:0] a, b, diff;
logic underflow;

math_subtractor_ripple_carry #(.N(8)) u_sub (
    .i_a(a), .i_b(b), .i_b_in(1'b0),
    .ow_d(diff), .ow_b(underflow)
);

// Borrow output indicates underflow (A < B)
// Example: 50 - 100 → underflow!
initial begin
    a = 8'd50;
    b = 8'd100;
    #1;
    assert(underflow == 1'b1);  // A < B
    assert(diff == 8'd206);     // Wraps around: 50 - 100 + 256 = 206
end
```

### Modern Approach: Subtraction Using Adder

```systemverilog
// PREFERRED: Use adder with two's complement
// A - B = A + (~B) + 1

logic [7:0] a, b, diff;
logic borrow;

math_adder_ripple_carry #(.N(8)) u_add (
    .i_a(a),
    .i_b(~b),          // Invert B (one's complement)
    .i_c(1'b1),        // Carry in = 1 (complete two's complement)
    .ow_sum(diff),
    .ow_carry(carry_out)
);

// Borrow = ~carry_out (inverted carry indicates underflow)
assign borrow = ~carry_out;
```

**Advantages of Adder-Based Subtraction:**
- Reuses existing adder hardware
- No separate subtractor needed
- Standard practice in modern ALUs
- Same timing characteristics

### Multi-Precision Subtraction (16-bit via 2×8-bit)

```systemverilog
logic [7:0] a_low, a_high, b_low, b_high;
logic [7:0] diff_low, diff_high;
logic borrow_low, borrow_high;

// Low byte
math_subtractor_ripple_carry #(.N(8)) u_sub_low (
    .i_a(a_low),
    .i_b(b_low),
    .i_b_in(1'b0),
    .ow_d(diff_low),
    .ow_b(borrow_low)
);

// High byte (chain borrow from low)
math_subtractor_ripple_carry #(.N(8)) u_sub_high (
    .i_a(a_high),
    .i_b(b_high),
    .i_b_in(borrow_low),
    .ow_d(diff_high),
    .ow_b(borrow_high)
);

logic [15:0] diff_16 = {diff_high, diff_low};
```

## Timing Characteristics

| Module | Logic Levels | Typical Delay (ns) |
|--------|--------------|-------------------|
| Half Subtractor | 1 | ~0.2 |
| Full Subtractor | 2 | ~0.4 |
| Ripple (N-bit) | 2N | ~0.4N |
| CLA (N-bit) | O(N) | Similar to ripple (simplified) |

**Note:** Subtractors have same timing as equivalent adders.

## Performance Characteristics

### Resource Utilization

| Module | LUTs | Description |
|--------|------|-------------|
| Half Subtractor | 2 | 1 XOR + 1 AND |
| Full Subtractor | 2 | Similar to full adder |
| Ripple (N-bit) | ~2N | N full subtractors |

### Subtractor vs Adder-Based Subtraction

| Aspect | Direct Subtractor | Adder + Two's Complement |
|--------|------------------|--------------------------|
| **Logic** | Dedicated subtractor cells | Reused adder + inverter |
| **Area** | +100% (separate unit) | +1% (just inverter) |
| **Timing** | Same as adder | Same as adder |
| **Modern Practice** | Rarely used | Standard approach |

## Design Considerations

### Why Adders Are Preferred for Subtraction

**Historical:** Separate subtractors were common in early designs.

**Modern:** Almost all designs use adders with two's complement:

**Advantages:**
- ✅ Hardware reuse (one adder for both add/subtract)
- ✅ Smaller area (no duplicate logic)
- ✅ Standard practice (easier to understand/maintain)
- ✅ ALU simplicity (single arithmetic unit)

**When to Use Direct Subtractors:**
- Educational/demonstration purposes
- Very specific applications requiring direct borrow propagation
- Compatibility with existing designs using subtractors

### Implementing Subtraction in ALU

```systemverilog
module simple_alu (
    input  logic [7:0] a, b,
    input  logic sub,  // 1 = subtract, 0 = add
    output logic [7:0] result,
    output logic carry_borrow
);

    logic [7:0] b_mux;
    logic cin_mux;

    // Two's complement: A - B = A + (~B) + 1
    assign b_mux = sub ? ~b : b;
    assign cin_mux = sub;

    math_adder_ripple_carry #(.N(8)) u_add (
        .i_a(a),
        .i_b(b_mux),
        .i_c(cin_mux),
        .ow_sum(result),
        .ow_carry(carry_out)
    );

    // For subtraction, borrow = ~carry
    assign carry_borrow = sub ? ~carry_out : carry_out;

endmodule
```

## Common Pitfalls

❌ **Anti-Pattern 1**: Using subtractors instead of adders

```systemverilog
// DISCOURAGED: Separate adder and subtractor
math_adder_ripple_carry u_add (...);
math_subtractor_ripple_carry u_sub (...);  // Duplicate hardware!

// PREFERRED: Single adder for both operations
math_adder_ripple_carry u_alu (
    .i_a(a),
    .i_b(sub ? ~b : b),  // Two's complement for subtraction
    .i_c(sub),
    ...
);
```

❌ **Anti-Pattern 2**: Ignoring borrow for underflow detection

```systemverilog
// WRONG: Ignoring borrow output
math_subtractor_ripple_carry u_sub (
    .i_a(a), .i_b(b), .i_b_in(1'b0),
    .ow_d(diff),
    .ow_b()  // IGNORED - miss underflow detection!
);

// RIGHT: Check borrow for underflow
logic underflow;
math_subtractor_ripple_carry u_sub (
    .i_a(a), .i_b(b), .i_b_in(1'b0),
    .ow_d(diff),
    .ow_b(underflow)  // Indicates A < B
);
```

❌ **Anti-Pattern 3**: Incorrect borrow interpretation

```systemverilog
// WRONG: Borrow means A < B, not A > B
if (borrow) begin
    // A is LESS than B (negative result)
end

// Remember: Borrow = 1 means underflow (A < B)
```

## Related Modules

- **math_adder_*.sv** - Preferred for subtraction via two's complement
- **math_addsub_full_nbit.sv** - Combined add/subtract unit

## References

- Mano, M.M. "Digital Design." Prentice Hall, 2002.
- Hennessy, J.L., Patterson, D.A. "Computer Architecture: A Quantitative Approach." Morgan Kaufmann, 2011.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
