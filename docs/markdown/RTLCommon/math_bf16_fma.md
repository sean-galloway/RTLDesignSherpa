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

# BF16 Fused Multiply-Add (FMA)

A BF16 Fused Multiply-Add unit with FP32 accumulator, designed for AI training workloads where maintaining precision during accumulation is critical.

## Overview

The `math_bf16_fma` module implements `result = (A * B) + C` as a single fused operation where A and B are BF16 inputs and C is an FP32 accumulator. This matches the computation pattern used in neural network training where weights and activations are BF16 but accumulated gradients need FP32 precision.

**Key Features:**
- **Mixed precision** - BF16 inputs (A, B), FP32 accumulator (C), FP32 output
- **Single fused operation** - No intermediate rounding between multiply and add
- **48-bit internal precision** - Captures full product + alignment bits
- **IEEE 754 special cases** - Zero, infinity, NaN handling
- **RNE rounding** - Round-to-Nearest-Even for unbiased results
- **FTZ mode** - Flush-to-Zero for subnormal inputs

## Module Declaration

```systemverilog
module math_bf16_fma(
    input  logic [15:0] i_a,           // BF16 multiplicand
    input  logic [15:0] i_b,           // BF16 multiplier
    input  logic [31:0] i_c,           // FP32 addend (accumulator)
    output logic [31:0] ow_result,     // FP32 result
    output logic        ow_overflow,   // Overflow to infinity
    output logic        ow_underflow,  // Underflow to zero
    output logic        ow_invalid     // Invalid operation
);
```

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_a | Input | 16 | BF16 multiplicand A |
| i_b | Input | 16 | BF16 multiplier B |
| i_c | Input | 32 | FP32 addend C (accumulator) |
| ow_result | Output | 32 | FP32 result = A * B + C |
| ow_overflow | Output | 1 | 1 if result overflowed to infinity |
| ow_underflow | Output | 1 | 1 if result underflowed to zero |
| ow_invalid | Output | 1 | 1 if operation was invalid |

## Format Specifications

### BF16 Format

```
BF16: [15]=sign, [14:7]=exponent (8 bits, bias=127), [6:0]=mantissa (7 bits)

Special values:
  +0:    0x0000 (sign=0, exp=0, mant=0)
  -0:    0x8000 (sign=1, exp=0, mant=0)
  +inf:  0x7F80 (sign=0, exp=255, mant=0)
  -inf:  0xFF80 (sign=1, exp=255, mant=0)
  NaN:   0x7FC0 (exp=255, mant!=0)
```

### FP32 Format

```
FP32: [31]=sign, [30:23]=exponent (8 bits, bias=127), [22:0]=mantissa (23 bits)

Special values:
  +0:    0x00000000
  -0:    0x80000000
  +inf:  0x7F800000
  -inf:  0xFF800000
  qNaN:  0x7FC00000 (canonical quiet NaN)
```

## Architecture

### Block Diagram

```
                    +----------------------------------------------------------+
                    |                    math_bf16_fma                         |
                    |                                                          |
    i_a[15:0] ------+--+-- sign_a ----+                                        |
    (BF16)          |  +-- exp_a -----+---------+                              |
                    |  +-- mant_a ---+|         |                              |
                    |                ||         |                              |
    i_b[15:0] ------+--+-- sign_b ---++-XOR-----+---- prod_sign                |
    (BF16)          |  +-- exp_b ----+|         |                              |
                    |  +-- mant_b --+||         |                              |
                    |               |||         |                              |
                    |   +-----------+||         |                              |
                    |   | 8x8 Dadda  ||         |                              |
                    |   | Multiplier ||         |    +-----------+             |
                    |   +-----------+||         +--->| Exponent  |             |
                    |        |      ||              | Compare & |             |
                    |        v      ||              | Alignment |             |
                    |   [15:0] prod ||              +-----------+             |
                    |        |      ||                    |                    |
                    |        v      ||                    v                    |
                    |   Extend to   ++----> exp_diff --> Shift smaller        |
                    |   48-bit      |                     operand              |
                    |        |      |                       |                  |
    i_c[31:0] ------+--------+------+                       |                  |
    (FP32)          |        |                              |                  |
                    |        v                              v                  |
                    |   +-------------------------------------------+          |
                    |   |      48-bit Han-Carlson Adder              |          |
                    |   |  (Structural, handles add/subtract)       |          |
                    |   +-------------------------------------------+          |
                    |                       |                                  |
                    |                       v                                  |
                    |   +-------------------------------------------+          |
                    |   |     Absolute Value (conditional negate)   |          |
                    |   |         (48-bit Han-Carlson)              |          |
                    |   +-------------------------------------------+          |
                    |                       |                                  |
                    |                       v                                  |
                    |   +-------------------------------------------+          |
                    |   |    Count Leading Zeros (Normalization)    |          |
                    |   |         (Bit-reversed CLZ)                |          |
                    |   +-------------------------------------------+          |
                    |                       |                                  |
                    |                       v                                  |
                    |   +-------------------------------------------+          |
                    |   |    Round-to-Nearest-Even (RNE)            |          |
                    |   |    Guard, Round, Sticky extraction        |          |
                    |   +-------------------------------------------+          |
                    |                       |                                  |
                    |                       v                                  |
                    |   +-------------------------------------------+          |
                    |   |        Special Case Priority MUX          |          |
                    |   |   NaN > Inf > Zero > Overflow > Normal    |          |
                    |   +-------------------------------------------+          |
                    |                       |                                  |
    ow_result[31:0] <-----------------------+                                  |
    ow_overflow <--------------------------------------------------------------|
    ow_underflow <-------------------------------------------------------------|
    ow_invalid <---------------------------------------------------------------|
                    +----------------------------------------------------------+
```

### Processing Pipeline

1. **Field Extraction** - Parse sign, exponent, mantissa from BF16 and FP32 inputs
2. **Special Case Detection** - Identify zero, subnormal, infinity, NaN for all inputs
3. **Product Computation** - 8x8 Dadda multiply for mantissas, exponent addition with bias correction
4. **Alignment** - Compare exponents, shift smaller operand to align
5. **Wide Addition** - 48-bit Han-Carlson add/subtract based on effective sign
6. **Absolute Value** - Conditional negate if subtraction result is negative
7. **Normalization** - Count leading zeros, shift left, adjust exponent
8. **RNE Rounding** - Extract guard/round/sticky, apply rounding
9. **Result Assembly** - Select output based on special case priority

## Functionality

### Mixed Precision Computation

```systemverilog
// BF16 product extended to 48-bit internal precision
wire [7:0] w_mant_a_ext = {w_a_is_normal, w_mant_a};  // 8-bit with implied 1
wire [7:0] w_mant_b_ext = {w_b_is_normal, w_mant_b};  // 8-bit with implied 1

// 8x8 -> 16-bit product, then extended to 48 bits
wire [15:0] w_prod_mant_raw;
wire [47:0] w_prod_mant_48 = {w_prod_mant_ext, 24'b0};

// FP32 addend extended to 48 bits
wire [23:0] w_c_mant_ext = w_c_is_normal ? {1'b1, w_mant_c} : 24'h0;
wire [47:0] w_c_mant_48  = {w_c_mant_ext, 24'b0};
```

### Exponent Alignment

```systemverilog
// Signed exponent difference for alignment
wire signed [10:0] w_exp_diff = $signed({1'b0, w_prod_exp}) -
                                $signed({1'b0, w_exp_c_ext});

// Shift smaller operand to align mantissas
wire [5:0] w_shift_clamped = (w_shift_amt > 10'd48) ? 6'd48 : w_shift_amt[5:0];
wire [47:0] w_mant_smaller_shifted = ... >> w_shift_clamped;
```

### Effective Addition/Subtraction

```systemverilog
// Effective operation based on signs
wire w_effective_sub = w_sign_larger ^ w_sign_smaller;

// Two's complement for subtraction
wire [47:0] w_adder_b = w_effective_sub ? ~w_mant_smaller_shifted
                                        : w_mant_smaller_shifted;

// 48-bit structural addition
math_adder_han_carlson_048 u_wide_adder (
    .i_a(w_mant_larger),
    .i_b(w_adder_b),
    .i_cin(w_effective_sub),  // +1 for two's complement
    .ow_sum(w_adder_sum),
    .ow_cout(w_adder_cout)
);
```

### Normalization with CLZ

```systemverilog
// Bit-reverse for leading zeros (CLZ module counts trailing zeros)
wire [47:0] w_sum_abs_reversed;
generate
    for (i = 0; i < 48; i = i + 1) begin : gen_bit_reverse
        assign w_sum_abs_reversed[i] = w_sum_abs[47 - i];
    end
endgenerate

count_leading_zeros #(.WIDTH(48)) u_clz (
    .data(w_sum_abs_reversed),
    .clz(w_lz_count_raw)
);

// Normalize: shift left, adjust exponent
wire [47:0] w_mant_normalized = w_sum_abs << w_lz_count;
wire signed [10:0] w_exp_adjusted = w_exp_result_pre - w_lz_count_raw + w_add_overflow;
```

### Special Case Priority

```systemverilog
always_comb begin
    // Priority order (highest to lowest):
    if (w_any_nan | w_invalid) begin
        // 1. NaN: any NaN input, or 0*inf, or inf-inf
        ow_result = {1'b0, 8'hFF, 23'h400000};  // Canonical qNaN
        ow_invalid = w_invalid;
    end else if (w_prod_is_inf & ~w_c_is_inf) begin
        // 2. Product infinity
        ow_result = {w_prod_sign, 8'hFF, 23'h0};
    end else if (w_c_is_inf) begin
        // 3. Addend infinity
        ow_result = {w_sign_c, 8'hFF, 23'h0};
    end else if (w_prod_is_zero) begin
        // 4. Zero product: pass-through addend
        ow_result = i_c;
    end else if (w_c_eff_zero) begin
        // 5. Zero addend: product only
        ow_result = {w_prod_sign, w_prod_exp[7:0], w_prod_mant_ext[22:0]};
    end else if (w_overflow_cond) begin
        // 6. Overflow to infinity
        ow_result = {w_result_sign, 8'hFF, 23'h0};
        ow_overflow = 1'b1;
    end else if (w_underflow_cond) begin
        // 7. Underflow to zero
        ow_result = {w_result_sign, 8'h00, 23'h0};
        ow_underflow = 1'b1;
    end
    // Default: normal result
end
```

## Usage Examples

### Basic FMA Operation

```systemverilog
logic [15:0] a, b;       // BF16 inputs
logic [31:0] c;          // FP32 accumulator
logic [31:0] result;
logic overflow, underflow, invalid;

math_bf16_fma u_fma (
    .i_a(a),
    .i_b(b),
    .i_c(c),
    .ow_result(result),
    .ow_overflow(overflow),
    .ow_underflow(underflow),
    .ow_invalid(invalid)
);

// Example: 2.0 * 3.0 + 1.0 = 7.0
// 2.0 in BF16: 0x4000
// 3.0 in BF16: 0x4040
// 1.0 in FP32: 0x3F800000
initial begin
    a = 16'h4000;           // 2.0
    b = 16'h4040;           // 3.0
    c = 32'h3F800000;       // 1.0
    #1;
    // result should be ~7.0 (0x40E00000)
end
```

### Neural Network Dot Product

```systemverilog
// Typical AI training pattern: accumulate weight * activation products
logic [15:0] weights[0:N-1];      // BF16 weights
logic [15:0] activations[0:N-1]; // BF16 activations
logic [31:0] accumulator;         // FP32 accumulator
logic [31:0] fma_result;

math_bf16_fma u_fma (
    .i_a(weights[idx]),
    .i_b(activations[idx]),
    .i_c(accumulator),
    .ow_result(fma_result),
    .ow_overflow(overflow),
    .ow_underflow(underflow),
    .ow_invalid(invalid)
);

// Accumulation loop
always_ff @(posedge clk) begin
    if (start)
        accumulator <= 32'h0;  // Initialize to zero
    else if (valid)
        accumulator <= fma_result;  // Accumulate
end
```

### With Pipeline Register

```systemverilog
// FMA is purely combinational - pipeline as needed for timing
logic [15:0] a_reg, b_reg;
logic [31:0] c_reg, result_reg;

always_ff @(posedge clk) begin
    // Input register stage
    a_reg <= a;
    b_reg <= b;
    c_reg <= c;
end

math_bf16_fma u_fma (
    .i_a(a_reg),
    .i_b(b_reg),
    .i_c(c_reg),
    .ow_result(result_comb),
    ...
);

always_ff @(posedge clk) begin
    // Output register stage
    result_reg <= result_comb;
end
```

## Timing Characteristics

| Stage | Logic Depth |
|-------|-------------|
| Field extraction | 0 (wiring) |
| Special case detection | 2 gates |
| 8x8 Dadda multiply | ~15 gates |
| Exponent compare/align | ~5 gates |
| 48-bit Han-Carlson add | ~8 stages |
| Absolute value (48-bit add) | ~8 stages |
| CLZ + normalization shift | ~6 gates |
| RNE rounding | ~3 gates |
| Result MUX | ~3 gates |
| **Total** | ~40-50 gates |

## Performance Characteristics

### Resource Utilization

| Component | LUTs (est.) |
|-----------|-------------|
| 8x8 Dadda multiplier | ~140 |
| 48-bit Han-Carlson adder (main) | ~250 |
| 48-bit Han-Carlson adder (negate) | ~250 |
| CLZ (48-bit) | ~50 |
| Alignment shifter | ~100 |
| Rounding logic | ~30 |
| Special case MUX | ~50 |
| **Total** | ~850-900 LUTs |

### Design Optimization Priorities

This module is optimized with the following priorities:
1. **Area** - Efficient submodule reuse (Dadda multiplier, Han-Carlson adders)
2. **Wire complexity** - Clean datapath with aligned internal widths
3. **Logic depth** - Parallel operations where possible

## Design Considerations

### Why FP32 Accumulator?

AI training requires maintaining precision during gradient accumulation:
- BF16 has only 7 mantissa bits (8-bit precision)
- Accumulating thousands of small values loses precision
- FP32 accumulator provides 23 mantissa bits
- Result can be truncated back to BF16 for storage if needed

### Fusion Benefits

Fused operation provides better accuracy than separate multiply-then-add:
- **Unfused:** `temp = A * B` (rounded), `result = temp + C` (rounded) - 2 rounding errors
- **Fused:** `result = A * B + C` (single rounding) - 1 rounding error
- Extra precision is maintained throughout the pipeline

### Product Underflow Handling

When the BF16 product exponent is too small:
```systemverilog
wire w_prod_underflow = w_prod_exp_adj[10] | (w_prod_exp_adj < 11'sd1);
wire w_prod_is_zero = w_a_eff_zero | w_b_eff_zero | w_prod_underflow;
```
Product underflow causes pass-through of the addend C.

### Invalid Operation Cases

Invalid operations produce NaN:
1. **0 * Infinity** - Indeterminate form
2. **Infinity - Infinity** - Indeterminate form (same magnitude, opposite signs)

```systemverilog
wire w_invalid_mul = (w_a_eff_zero & w_b_is_inf) | (w_b_eff_zero & w_a_is_inf);
wire w_invalid_add = w_prod_is_inf & w_c_is_inf & (w_prod_sign != w_sign_c);
```

## Common Pitfalls

**Anti-Pattern 1:** Using BF16 accumulator
```systemverilog
// WRONG: Precision loss in accumulation
logic [15:0] bf16_accum;  // Only 7 mantissa bits!

// RIGHT: Use FP32 accumulator
logic [31:0] fp32_accum;  // 23 mantissa bits
```

**Anti-Pattern 2:** Ignoring special cases
```systemverilog
// WRONG: Assuming result is always valid
output_reg <= result;

// RIGHT: Check status flags
if (invalid)
    handle_nan();
else if (overflow)
    handle_infinity();
else
    output_reg <= result;
```

**Anti-Pattern 3:** Expecting subnormal outputs
```systemverilog
// NOTE: FTZ mode flushes tiny results to zero
// If gradients become very small, they flush to zero
// This is intentional for AI training efficiency
```

## Auto-Generated Code

This module is auto-generated by Python scripts:
- **Generator:** `bin/rtl_generators/bf16/bf16_fma.py`
- **Regenerate:** `PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/generate_all.py rtl/common`

**Do not edit the generated .sv file manually.**

## Related Modules

- **math_multiplier_dadda_4to2_008** - 8x8 Dadda multiplier used for mantissa
- **math_adder_han_carlson_048** - 48-bit adder for wide addition
- **count_leading_zeros** - Normalization support
- **math_bf16_multiplier** - Standalone BF16 multiplier (simpler, no accumulate)
- **math_bf16_mantissa_mult** - Mantissa multiplication submodule
- **math_bf16_exponent_adder** - Exponent computation submodule

## References

- Google Brain Float (BF16) specification
- IEEE 754-2019 Standard for Floating-Point Arithmetic
- Intel BFloat16 documentation
- NVIDIA TensorFloat documentation
- Muller, J.M. et al. "Handbook of Floating-Point Arithmetic." Birkhauser, 2018.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
