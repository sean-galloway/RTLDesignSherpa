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

# IEEE 754-2008 Compliant Modules

Full IEEE 754-2008 compliant floating-point arithmetic modules for FP16 and FP32 formats.

## Overview

These modules implement complete IEEE 754-2008 compliant arithmetic for half-precision (FP16) and single-precision (FP32) floating-point operations. Unlike the simplified BF16/FP8 modules which use Flush-to-Zero, these provide proper subnormal handling and full IEEE compliance.

**Key Features:**
- **Full IEEE 754-2008 compliance** - Proper subnormal handling, all rounding modes conceptually supported
- **Complete special case handling** - Zero, infinity, NaN, subnormal
- **Status flags** - Overflow, underflow, invalid, inexact
- **Pipelined options** - Configurable pipeline stages for timing closure

## Module Summary

### FP16 (Half Precision) IEEE 754

| Module | Operation | Description |
|--------|-----------|-------------|
| `math_ieee754_2008_fp16_adder` | a + b | Full FP16 addition with alignment |
| `math_ieee754_2008_fp16_multiplier` | a * b | FP16 multiplication |
| `math_ieee754_2008_fp16_fma` | a*b + c | Fused multiply-add |
| `math_ieee754_2008_fp16_mantissa_mult` | Internal | 11x11 mantissa multiply |
| `math_ieee754_2008_fp16_exponent_adder` | Internal | Exponent computation |

### FP32 (Single Precision) IEEE 754

| Module | Operation | Description |
|--------|-----------|-------------|
| `math_ieee754_2008_fp32_adder` | a + b | Full FP32 addition with alignment |
| `math_ieee754_2008_fp32_multiplier` | a * b | FP32 multiplication |
| `math_ieee754_2008_fp32_fma` | a*b + c | Fused multiply-add |
| `math_ieee754_2008_fp32_mantissa_mult` | Internal | 24x24 mantissa multiply |
| `math_ieee754_2008_fp32_exponent_adder` | Internal | Exponent computation |

## Module Interfaces

### FP16 Adder

```systemverilog
module math_ieee754_2008_fp16_adder #(
    parameter int PIPE_STAGE_1 = 0,  // After operand swap
    parameter int PIPE_STAGE_2 = 0,  // After alignment
    parameter int PIPE_STAGE_3 = 0,  // After addition
    parameter int PIPE_STAGE_4 = 0   // After normalization
) (
    input  logic        i_clk,
    input  logic        i_rst_n,
    input  logic [15:0] i_a,
    input  logic [15:0] i_b,
    input  logic        i_valid,
    output logic [15:0] ow_result,
    output logic        ow_valid,
    output logic        ow_overflow,
    output logic        ow_underflow,
    output logic        ow_invalid
);
```

### FP32 Multiplier

```systemverilog
module math_ieee754_2008_fp32_multiplier (
    input  logic [31:0] i_a,
    input  logic [31:0] i_b,
    output logic [31:0] ow_result,
    output logic        ow_overflow,
    output logic        ow_underflow,
    output logic        ow_invalid
);
```

### FP32 FMA

```systemverilog
module math_ieee754_2008_fp32_fma (
    input  logic [31:0] i_a,      // Multiplicand
    input  logic [31:0] i_b,      // Multiplier
    input  logic [31:0] i_c,      // Addend
    output logic [31:0] ow_result,
    output logic        ow_overflow,
    output logic        ow_underflow,
    output logic        ow_invalid
);
```

## Architecture

### FP32 Multiplier Pipeline

```
Stage 1: Field extraction + special case detection
         sign_a, exp_a[7:0], mant_a[22:0]
         sign_b, exp_b[7:0], mant_b[22:0]
              |
Stage 2: Sign computation (XOR)
         24x24 Dadda tree multiplication -> 48-bit product
              |
Stage 3: Exponent computation
         exp_sum = exp_a + exp_b - 127 + norm_adjust
              |
Stage 4: Normalization + RNE rounding
         Shift product, apply round-to-nearest-even
              |
Stage 5: Special case priority selection
         NaN > Inf > Overflow > Underflow > Zero > Normal
              |
         Result assembly
```

### FP32 FMA Architecture

```
                 ┌─────────────────────────────────────────┐
                 │         FP32 FMA (a*b + c)              │
                 │                                         │
    i_a[31:0] ───┼──► 24x24 Multiplier ──► 48-bit product │
    i_b[31:0] ───┼──►                                     │
                 │                                         │
    i_c[31:0] ───┼──► Alignment Shifter ──► 72-bit aligned│
                 │                                         │
                 │   ┌───────────────────────────────────┐ │
                 │   │ 72-bit Wide Adder                 │ │
                 │   │ (Han-Carlson prefix adder)        │ │
                 │   └───────────────────────────────────┘ │
                 │                   │                     │
                 │   ┌───────────────┴───────────────────┐ │
                 │   │ 72-bit CLZ + Normalization        │ │
                 │   └───────────────────────────────────┘ │
                 │                   │                     │
                 │   ┌───────────────┴───────────────────┐ │
                 │   │ RNE Rounding to FP32              │ │
                 │   └───────────────────────────────────┘ │
                 │                   │                     │
 ow_result[31:0] ◄───────────────────┘                     │
                 └─────────────────────────────────────────┘
```

## IEEE 754 Compliance

### Special Value Handling

| Operation | Input | Output |
|-----------|-------|--------|
| Any | NaN | NaN (propagated) |
| x + y | +Inf, -Inf | NaN (invalid) |
| x * y | 0, Inf | NaN (invalid) |
| x + y | Normal, Normal | Normal/Subnormal |
| x * y | Normal, Normal | Normal/Subnormal/Zero |

### Rounding Modes

Currently implements Round-to-Nearest-Even (RNE):
```systemverilog
// RNE: Round up if guard=1 AND (round=1 OR sticky=1 OR lsb=1)
wire w_round_up = w_guard & (w_round | w_sticky | w_lsb);
```

### Status Flags

| Flag | Condition |
|------|-----------|
| `ow_overflow` | Result magnitude exceeds max normal |
| `ow_underflow` | Result magnitude less than min normal (non-zero) |
| `ow_invalid` | Invalid operation (0*Inf, Inf-Inf, NaN input) |

## Comparison: IEEE 754 vs Simplified Modules

| Feature | IEEE 754 Modules | BF16/FP8 Modules |
|---------|------------------|------------------|
| Subnormals | Full support | Flush to Zero |
| Infinity | Proper handling | Saturation (FP8 E4M3) |
| NaN payloads | Preserved | Canonical only |
| Rounding modes | RNE (extensible) | RNE only |
| Pipeline options | Configurable | Fixed |
| Target use | Precision-critical | AI/ML acceleration |

## Usage Examples

### High-Precision Computation

```systemverilog
// IEEE 754 compliant FP32 FMA for numerical accuracy
logic [31:0] a, b, c, result;

math_ieee754_2008_fp32_fma u_fma (
    .i_a(a),
    .i_b(b),
    .i_c(c),
    .ow_result(result),
    .ow_overflow(overflow),
    .ow_underflow(underflow),
    .ow_invalid(invalid)
);

// Check for exceptions
always_ff @(posedge clk) begin
    if (invalid)
        $error("Invalid FP operation!");
    else if (overflow)
        $warning("FP overflow - result is infinity");
end
```

### Pipelined FP16 Adder

```systemverilog
// 4-stage pipelined FP16 adder for high frequency
math_ieee754_2008_fp16_adder #(
    .PIPE_STAGE_1(1),  // Pipeline after swap
    .PIPE_STAGE_2(1),  // Pipeline after align
    .PIPE_STAGE_3(1),  // Pipeline after add
    .PIPE_STAGE_4(1)   // Pipeline after normalize
) u_adder (
    .i_clk(clk),
    .i_rst_n(rst_n),
    .i_a(fp16_a),
    .i_b(fp16_b),
    .i_valid(input_valid),
    .ow_result(fp16_sum),
    .ow_valid(output_valid),
    .ow_overflow(),
    .ow_underflow(),
    .ow_invalid()
);
```

## Dependencies

These modules use the following building blocks:

| Module | Used By | Purpose |
|--------|---------|---------|
| `math_adder_han_carlson_072` | FP32 FMA | 72-bit wide addition |
| `math_adder_han_carlson_048` | FP32 mult | 48-bit product CPA |
| `math_multiplier_dadda_4to2_024` | FP32 | 24x24 mantissa multiply |
| `math_multiplier_dadda_4to2_011` | FP16 | 11x11 mantissa multiply |
| `count_leading_zeros` | All | Normalization |
| `shifter_barrel` | Adders | Mantissa alignment |

## Auto-Generation

```bash
# Regenerate IEEE 754 modules
PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
```

**Generator files:**
- `bin/rtl_generators/ieee754/fp16_adder.py`
- `bin/rtl_generators/ieee754/fp16_multiplier.py`
- `bin/rtl_generators/ieee754/fp16_fma.py`
- `bin/rtl_generators/ieee754/fp32_adder.py`
- `bin/rtl_generators/ieee754/fp32_multiplier.py`
- `bin/rtl_generators/ieee754/fp32_fma.py`

## Related Documentation

- **[math_bf16_multiplier](math_bf16_multiplier.md)** - Simplified BF16 multiply
- **[math_bf16_fma](math_bf16_fma.md)** - Simplified BF16 FMA
- **[math_adder_han_carlson](math_adder_han_carlson.md)** - Prefix adder building block
- **[math_multiplier_dadda_4to2](math_multiplier_dadda_4to2.md)** - Dadda multiplier

## Navigation

- **[Back to RTLCommon Index](index.md)**
- **[Back to Main Documentation Index](../../index.md)**
