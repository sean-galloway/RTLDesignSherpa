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

# BF16 Exponent Adder

An exponent computation module for BF16 multiplication that handles bias subtraction, normalization adjustment, overflow/underflow detection, and special value identification.

## Overview

The `math_bf16_exponent_adder` module computes the result exponent for BF16 multiplication using the formula: `exp_result = exp_a + exp_b - bias + norm_adjust`. It uses extended precision arithmetic to detect overflow and underflow conditions before they occur.

**Key Features:**
- **Bias-compensated addition** - Handles 127 bias subtraction
- **Normalization adjustment** - +1 when mantissa product >= 2.0
- **Overflow detection** - Flags when result > 254
- **Underflow detection** - Flags when result <= 0
- **Special case flags** - Identifies zero, infinity, and NaN inputs

## Module Declaration

```systemverilog
module math_bf16_exponent_adder(
    input  logic [7:0] i_exp_a,        // 8-bit exponent A
    input  logic [7:0] i_exp_b,        // 8-bit exponent B
    input  logic       i_norm_adjust,  // +1 if mantissa needs normalization
    output logic [7:0] ow_exp_out,     // 8-bit result exponent
    output logic       ow_overflow,    // Exponent overflow (result = inf)
    output logic       ow_underflow,   // Exponent underflow (result = zero)
    output logic       ow_a_is_zero,   // Input A has zero exponent
    output logic       ow_b_is_zero,   // Input B has zero exponent
    output logic       ow_a_is_inf,    // Input A has max exponent
    output logic       ow_b_is_inf,    // Input B has max exponent
    output logic       ow_a_is_nan,    // Input A has max exponent (NaN check)
    output logic       ow_b_is_nan     // Input B has max exponent (NaN check)
);
```

## Ports

### Inputs

| Port | Width | Description |
|------|-------|-------------|
| i_exp_a | 8 | Biased exponent of operand A |
| i_exp_b | 8 | Biased exponent of operand B |
| i_norm_adjust | 1 | +1 adjustment when mantissa product >= 2.0 |

### Outputs

| Port | Width | Description |
|------|-------|-------------|
| ow_exp_out | 8 | Result exponent (saturated on overflow/underflow) |
| ow_overflow | 1 | 1 if result exponent > 254 (infinity) |
| ow_underflow | 1 | 1 if result exponent <= 0 (zero) |
| ow_a_is_zero | 1 | 1 if exp_a == 0 (caller checks mantissa) |
| ow_b_is_zero | 1 | 1 if exp_b == 0 (caller checks mantissa) |
| ow_a_is_inf | 1 | 1 if exp_a == 255 (caller checks mantissa for NaN) |
| ow_b_is_inf | 1 | 1 if exp_b == 255 (caller checks mantissa for NaN) |
| ow_a_is_nan | 1 | Same as ow_a_is_inf (actual NaN needs mantissa != 0) |
| ow_b_is_nan | 1 | Same as ow_b_is_inf (actual NaN needs mantissa != 0) |

## BF16 Exponent Background

### BF16 Format

```
BF16: [15]=sign, [14:7]=exponent (8 bits, bias=127), [6:0]=mantissa (7 bits)

Exponent encoding:
  exp = 0:   Zero (if mantissa=0) or Subnormal (if mantissa!=0)
  exp = 255: Infinity (if mantissa=0) or NaN (if mantissa!=0)
  exp = 1-254: Normal number, actual exponent = exp - 127
```

### Multiplication Exponent Formula

For floating-point multiplication:
```
result = A * B
       = (2^(exp_a - 127) * mant_a) * (2^(exp_b - 127) * mant_b)
       = 2^(exp_a + exp_b - 254) * (mant_a * mant_b)

If mantissa product >= 2.0, normalize by right-shifting mantissa and adding 1 to exponent:
       = 2^(exp_a + exp_b - 254 + 1) * (mant_a * mant_b / 2)

Biased result exponent = exp_a + exp_b - 127 + norm_adjust
```

## Functionality

### Special Case Detection

```systemverilog
// Zero exponent: input is zero or subnormal
assign ow_a_is_zero = (i_exp_a == 8'h00);
assign ow_b_is_zero = (i_exp_b == 8'h00);

// Max exponent: input is infinity or NaN
assign ow_a_is_inf = (i_exp_a == 8'hFF);
assign ow_b_is_inf = (i_exp_b == 8'hFF);

// NaN detection requires mantissa check (done by caller)
assign ow_a_is_nan = (i_exp_a == 8'hFF);
assign ow_b_is_nan = (i_exp_b == 8'hFF);
```

**Note:** The module reports exp==255 as both "inf" and "nan" - the caller must check the mantissa to distinguish.

### Extended Precision Arithmetic

```systemverilog
// Use 10-bit arithmetic to detect overflow/underflow before they happen
wire [9:0] w_exp_sum_raw;

// exp_a + exp_b + norm_adjust - 127
assign w_exp_sum_raw = {2'b0, i_exp_a} + {2'b0, i_exp_b} +
                       {9'b0, i_norm_adjust} - 10'd127;
```

**Why 10 bits?**
- Maximum sum: 255 + 255 + 1 = 511 (needs 9 bits)
- After subtracting 127: 511 - 127 = 384 (still fits in 9 bits)
- Need 10th bit to detect negative results (underflow)

### Overflow/Underflow Detection

```systemverilog
// Underflow: result <= 0 (MSB set means negative, or result is exactly 0)
wire w_underflow_raw = w_exp_sum_raw[9] | (w_exp_sum_raw == 10'd0);

// Overflow: result > 254 (255 is reserved for inf/nan)
// Only valid if not underflow (negative values wrap to large positive)
wire w_overflow_raw = ~w_underflow_raw & (w_exp_sum_raw > 10'd254);

// Special cases override normal overflow/underflow
wire w_either_special = ow_a_is_inf | ow_b_is_inf | ow_a_is_zero | ow_b_is_zero;

assign ow_overflow  = w_overflow_raw & ~w_either_special;
assign ow_underflow = w_underflow_raw & ~w_either_special;
```

**Key insight:** Must check underflow BEFORE overflow because negative values (underflow) appear as large positive values in unsigned arithmetic.

### Result Saturation

```systemverilog
always_comb begin
    if (ow_overflow) begin
        ow_exp_out = 8'hFF;  // Saturate to infinity
    end else if (ow_underflow) begin
        ow_exp_out = 8'h00;  // Saturate to zero
    end else begin
        ow_exp_out = w_exp_sum_raw[7:0];  // Normal result
    end
end
```

## Usage Examples

### Basic Usage

```systemverilog
logic [7:0] exp_a, exp_b;
logic       norm_adjust;
logic [7:0] exp_result;
logic       overflow, underflow;
logic       a_zero, b_zero, a_inf, b_inf;

math_bf16_exponent_adder u_exp_add (
    .i_exp_a(exp_a),
    .i_exp_b(exp_b),
    .i_norm_adjust(norm_adjust),
    .ow_exp_out(exp_result),
    .ow_overflow(overflow),
    .ow_underflow(underflow),
    .ow_a_is_zero(a_zero),
    .ow_b_is_zero(b_zero),
    .ow_a_is_inf(a_inf),
    .ow_b_is_inf(b_inf),
    .ow_a_is_nan(),   // Use with mantissa check
    .ow_b_is_nan()
);
```

### In BF16 Multiplier

```systemverilog
// Get normalization flag from mantissa multiplier
wire w_needs_norm;
math_bf16_mantissa_mult u_mant_mult (..., .ow_needs_norm(w_needs_norm), ...);

// Compute exponent
math_bf16_exponent_adder u_exp_add (
    .i_exp_a(i_a[14:7]),
    .i_exp_b(i_b[14:7]),
    .i_norm_adjust(w_needs_norm),
    .ow_exp_out(w_exp_result),
    .ow_overflow(w_exp_overflow),
    .ow_underflow(w_exp_underflow),
    ...
);

// Handle rounding-induced exponent overflow
wire w_mant_round_overflow = ...;  // From mantissa rounding
wire [7:0] w_exp_final = w_mant_round_overflow ? (w_exp_result + 8'd1)
                                               : w_exp_result;
wire w_final_overflow = w_exp_overflow | (w_exp_final == 8'hFF);
```

### Example Calculations

| exp_a | exp_b | norm_adj | Calculation | Result | Status |
|-------|-------|----------|-------------|--------|--------|
| 127 | 127 | 0 | 127 + 127 - 127 + 0 = 127 | 127 | Normal |
| 127 | 127 | 1 | 127 + 127 - 127 + 1 = 128 | 128 | Normal |
| 200 | 200 | 0 | 200 + 200 - 127 + 0 = 273 | 255 | Overflow |
| 50 | 50 | 0 | 50 + 50 - 127 + 0 = -27 | 0 | Underflow |
| 1 | 1 | 0 | 1 + 1 - 127 + 0 = -125 | 0 | Underflow |

## Timing Characteristics

| Path | Logic Depth |
|------|-------------|
| Special case detection | 1 gate (comparator) |
| Exponent addition | 2-3 gates (10-bit add) |
| Overflow/underflow detection | 2 gates (compare + AND) |
| Result MUX | 1 gate |
| **Total** | ~5-7 gate levels |

## Performance Characteristics

### Resource Utilization

| Component | LUTs (est.) |
|-----------|-------------|
| 10-bit adder | ~15 |
| Comparators | ~10 |
| Output MUX | ~8 |
| Special case flags | ~4 |
| **Total** | ~35-40 LUTs |

### Design Optimization Priorities

This module is optimized with the following priorities:
1. **Area** - Simple 10-bit arithmetic instead of full-width operations
2. **Wire complexity** - Minimal signal routing
3. **Logic depth** - Parallel overflow/underflow detection

## Design Considerations

### Why Override Flags for Special Cases?

When either input is zero or infinity, the overflow/underflow flags shouldn't trigger the normal saturation path:
- **Zero * anything** -> Zero (handled by caller, not underflow)
- **Infinity * anything** -> Infinity (handled by caller, not overflow)
- **0 * Infinity** -> NaN (invalid operation, handled by caller)

The flags are suppressed to let the caller handle these cases explicitly.

### Exponent Ranges

| Biased exp | Meaning | Result |
|------------|---------|--------|
| 0 | Zero/Subnormal | Treat as zero (FTZ) |
| 1-254 | Normal | Valid computation |
| 255 | Inf/NaN | Special handling |

### Order of Checks

The module checks underflow BEFORE overflow because:
1. Negative results (e.g., -25) appear as large positive values (e.g., 999) in unsigned math
2. Without underflow check first, -25 would incorrectly trigger overflow

## Auto-Generated Code

This module is auto-generated by Python scripts:
- **Generator:** `bin/rtl_generators/bf16/bf16_exponent_adder.py`
- **Regenerate:** `PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/generate_all.py rtl/common`

**Do not edit the generated .sv file manually.**

## Related Modules

- **math_bf16_mantissa_mult** - Companion mantissa handling
- **math_bf16_multiplier** - Complete BF16 multiplier using this module
- **math_bf16_fma** - BF16 FMA with similar exponent logic

## References

- IEEE 754-2019 Standard for Floating-Point Arithmetic
- Google Brain Float (BF16) specification
- Muller, J.M. et al. "Handbook of Floating-Point Arithmetic." Birkhauser, 2018.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
