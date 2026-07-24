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

# BF16 Mantissa Multiplier

A specialized mantissa multiplier for BF16 (Brain Float 16) format that handles implied leading 1, normalization detection, and rounding bit extraction for IEEE 754-compliant floating-point multiplication.

## Overview

The `math_bf16_mantissa_mult` module wraps an 8x8 Dadda multiplier with BF16-specific logic for handling the implicit leading bit, detecting when normalization is needed, and extracting guard/round/sticky bits for Round-to-Nearest-Even (RNE) rounding.

**Key Features:**
- **8x8 unsigned multiply** - 7-bit mantissa + 1 implied bit
- **Normalization detection** - Flags when product >= 2.0
- **Mantissa extraction** - Selects correct 7 bits based on normalization
- **Rounding support** - Provides round and sticky bits for RNE
- **FTZ mode** - Handles subnormal inputs as zero

## Module Declaration

```systemverilog
module math_bf16_mantissa_mult(
    input  logic [6:0]  i_mant_a,      // 7-bit explicit mantissa A
    input  logic [6:0]  i_mant_b,      // 7-bit explicit mantissa B
    input  logic        i_a_is_normal, // A has implied leading 1
    input  logic        i_b_is_normal, // B has implied leading 1
    output logic [15:0] ow_product,    // 16-bit raw product
    output logic        ow_needs_norm, // 1 if product >= 2.0
    output logic [6:0]  ow_mant_out,   // 7-bit result mantissa
    output logic        ow_round_bit,  // Round bit for RNE
    output logic        ow_sticky_bit  // Sticky bit for RNE
);
```

## Ports

### Inputs

| Port | Width | Description |
|------|-------|-------------|
| i_mant_a | 7 | Explicit mantissa of operand A (bits [6:0] of BF16) |
| i_mant_b | 7 | Explicit mantissa of operand B (bits [6:0] of BF16) |
| i_a_is_normal | 1 | 1 if A is normalized (has implied leading 1) |
| i_b_is_normal | 1 | 1 if B is normalized (has implied leading 1) |

### Outputs

| Port | Width | Description |
|------|-------|-------------|
| ow_product | 16 | Full 16-bit raw product from 8x8 multiply |
| ow_needs_norm | 1 | 1 if product >= 2.0 (MSB of product is 1) |
| ow_mant_out | 7 | Pre-rounded 7-bit mantissa result |
| ow_round_bit | 1 | Round bit for RNE rounding |
| ow_sticky_bit | 1 | Sticky bit for RNE rounding |

## BF16 Format Background

### BF16 Structure

```
BF16: [15]=sign, [14:7]=exponent (8 bits), [6:0]=mantissa (7 bits)

For normalized numbers (exp != 0 and exp != 255):
  Value = (-1)^sign * 2^(exp-127) * 1.mantissa

The "1." is implicit (not stored), so actual mantissa is 8 bits: {1, mantissa[6:0]}
```

### Mantissa Multiplication

When multiplying two normalized BF16 numbers:
- Operand A mantissa: `1.aaaaaaa` (8 bits with implicit 1)
- Operand B mantissa: `1.bbbbbbb` (8 bits with implicit 1)
- Product: 16-bit result in range [1.0, 4.0)

**Product format:**
- If product >= 2.0: `1x.xxxxxx_xxxxxxxx` (needs right shift + exp++)
- If product < 2.0: `01.xxxxxx_xxxxxxxx` (no shift needed)

## Functionality

### Mantissa Extension

```systemverilog
// Extend 7-bit explicit mantissa with implied leading 1
wire [7:0] w_mant_a_ext = {i_a_is_normal, i_mant_a};
wire [7:0] w_mant_b_ext = {i_b_is_normal, i_mant_b};
```

For normal numbers, this creates `1.mantissa`. For zeros/subnormals (FTZ mode), creates `0.mantissa` which effectively treats them as zero.

### 8x8 Multiplication

```systemverilog
math_multiplier_dadda_4to2_008 u_mult (
    .i_multiplier(w_mant_a_ext),
    .i_multiplicand(w_mant_b_ext),
    .ow_product(ow_product)
);
```

### Normalization Detection

```systemverilog
// MSB set means product >= 2.0, needs right shift
assign ow_needs_norm = ow_product[15];
```

### Mantissa Extraction

```systemverilog
// Extract 7-bit mantissa based on normalization state
assign ow_mant_out = ow_needs_norm ? ow_product[14:8]  // Shifted right
                                   : ow_product[13:7]; // No shift
```

**Product bit mapping:**

| Product format | Implied 1 | Mantissa bits | Guard | Round | Sticky |
|----------------|-----------|---------------|-------|-------|--------|
| Needs norm (MSB=1) | [15] | [14:8] | [7] | [6] | [5:0] |
| No norm (MSB=0) | [14] | [13:7] | [6] | [5] | [4:0] |

### Rounding Bits for RNE

```systemverilog
// Guard, round, sticky for RNE rounding
wire w_guard_norm    = ow_product[7];
wire w_guard_nonorm  = ow_product[6];

wire w_round_norm    = ow_product[6];
wire w_round_nonorm  = ow_product[5];

wire w_sticky_norm   = |ow_product[5:0];
wire w_sticky_nonorm = |ow_product[4:0];

assign ow_round_bit  = ow_needs_norm ? w_round_norm  : w_round_nonorm;
assign ow_sticky_bit = ow_needs_norm ?
    (w_guard_norm | w_sticky_norm) : (w_guard_nonorm | w_sticky_nonorm);
```

**Note:** The sticky bit includes the guard bit because after mantissa extraction, the guard becomes part of the "remaining" bits for rounding purposes.

## Usage Examples

### Basic Usage

```systemverilog
logic [6:0] mant_a, mant_b;
logic       a_normal, b_normal;
logic [15:0] product;
logic        needs_norm;
logic [6:0]  mant_result;
logic        round_bit, sticky_bit;

math_bf16_mantissa_mult u_mant_mult (
    .i_mant_a(mant_a),
    .i_mant_b(mant_b),
    .i_a_is_normal(a_normal),
    .i_b_is_normal(b_normal),
    .ow_product(product),
    .ow_needs_norm(needs_norm),
    .ow_mant_out(mant_result),
    .ow_round_bit(round_bit),
    .ow_sticky_bit(sticky_bit)
);
```

### In BF16 Multiplier

```systemverilog
// Extract fields from BF16 inputs
wire [6:0] w_mant_a = i_a[6:0];
wire [6:0] w_mant_b = i_b[6:0];
wire       w_a_is_normal = (i_a[14:7] != 8'h00) & (i_a[14:7] != 8'hFF);
wire       w_b_is_normal = (i_b[14:7] != 8'h00) & (i_b[14:7] != 8'hFF);

// Mantissa multiplication
math_bf16_mantissa_mult u_mant_mult (
    .i_mant_a(w_mant_a),
    .i_mant_b(w_mant_b),
    .i_a_is_normal(w_a_is_normal),
    .i_b_is_normal(w_b_is_normal),
    .ow_product(w_product),
    .ow_needs_norm(w_needs_norm),
    .ow_mant_out(w_mant_mult_out),
    .ow_round_bit(w_round_bit),
    .ow_sticky_bit(w_sticky_bit)
);

// Apply RNE rounding
wire w_lsb = w_mant_mult_out[0];
wire w_round_up = w_round_bit & (w_sticky_bit | w_lsb);
wire [7:0] w_mant_rounded = {1'b0, w_mant_mult_out} + {7'b0, w_round_up};

// Check for mantissa overflow from rounding
wire w_mant_overflow = w_mant_rounded[7];
wire [6:0] w_mant_final = w_mant_overflow ? 7'h00 : w_mant_rounded[6:0];
```

## Timing Characteristics

| Stage | Logic Depth |
|-------|-------------|
| Mantissa extension | 0 (just wiring) |
| 8x8 Dadda multiply | ~13-15 gates |
| Normalization detection | 1 gate (wire to MSB) |
| Mantissa MUX | 1 gate |
| Round/sticky OR | 1 gate |
| **Total** | ~15-17 gates |

## Performance Characteristics

### Resource Utilization

| Component | Resource |
|-----------|----------|
| 8x8 Multiplier | ~120-140 LUTs |
| Normalization MUX | ~14 LUTs |
| Rounding logic | ~10 LUTs |
| **Total** | ~140-165 LUTs |

### Design Optimization Priorities

This module is optimized with the following priorities:
1. **Area** - Minimal overhead over raw multiplier
2. **Wire complexity** - Simple MUXing for normalization
3. **Logic depth** - Normalization adds only 1 gate level

## Design Considerations

### Flush-to-Zero (FTZ) Mode

Subnormal inputs (exp=0, mantissa!=0) are treated as zero:
- `i_a_is_normal` or `i_b_is_normal` will be 0
- Extended mantissa becomes `{0, mantissa}` instead of `{1, mantissa}`
- Product will be effectively zero

This matches standard BF16 behavior in AI accelerators.

### Why Separate from Multiplier?

This wrapper is separate from the raw multiplier because:
1. **Reusability** - Raw multiplier can be used elsewhere
2. **Testability** - Each component can be tested independently
3. **Clarity** - BF16-specific logic is isolated

### Round-to-Nearest-Even

The rounding bits support IEEE 754 RNE:
```
Round up if: Guard AND (Round OR Sticky OR LSB)
```
This ensures ties (exactly halfway) round to even.

## Auto-Generated Code

This module is auto-generated by Python scripts:
- **Generator:** `bin/rtl_generators/bf16/bf16_mantissa_mult.py`
- **Regenerate:** `PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/generate_all.py rtl/common`

**Do not edit the generated .sv file manually.**

## Related Modules

- **math_multiplier_dadda_4to2_008** - Underlying 8x8 multiplier
- **math_bf16_exponent_adder** - Companion exponent handling
- **math_bf16_multiplier** - Complete BF16 multiplier using this module
- **math_bf16_fma** - BF16 FMA also uses Dadda multiplier directly

## References

- Google Brain Float (BF16) specification
- IEEE 754-2019 Standard for Floating-Point Arithmetic
- Muller, J.M. et al. "Handbook of Floating-Point Arithmetic." Birkhauser, 2018.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
