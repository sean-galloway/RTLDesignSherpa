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

# FP16 (Half Precision) Modules

IEEE 754 half-precision (FP16) floating-point modules for activation functions, comparison, and format conversion.

## Overview

FP16 (16-bit floating-point) provides higher precision than BF16 with a different exponent/mantissa trade-off. These modules complement the BF16 library for applications requiring greater precision in the fractional range.

**FP16 Format:**
```
[15]    = Sign bit
[14:10] = Exponent (5 bits, bias = 15)
[9:0]   = Mantissa (10 bits, implicit leading 1)

Range: ~6.0e-8 to ~65504
Precision: ~0.1% (3-4 decimal digits)
```

**Key Differences from BF16:**
| Property | BF16 | FP16 |
|----------|------|------|
| Exponent bits | 8 | 5 |
| Mantissa bits | 7 | 10 |
| Dynamic range | Same as FP32 | Limited (~65504 max) |
| Precision | ~1% | ~0.1% |

## Module Categories

### Activation Functions

| Module | Function | Description |
|--------|----------|-------------|
| `math_fp16_relu` | max(0, x) | Rectified Linear Unit |
| `math_fp16_leaky_relu` | max(0.01x, x) | Leaky ReLU |
| `math_fp16_gelu` | x * Phi(x) | Gaussian Error Linear Unit |
| `math_fp16_sigmoid` | 1/(1+exp(-x)) | Logistic function |
| `math_fp16_tanh` | tanh(x) | Hyperbolic tangent |
| `math_fp16_silu` | x * sigmoid(x) | SiLU/Swish activation |
| `math_fp16_softmax_8` | softmax(x[7:0]) | 8-input softmax |

#### Interface

```systemverilog
module math_fp16_{activation} (
    input  logic [15:0] i_a,        // FP16 input
    output logic [15:0] ow_result   // FP16 output
);
```

### Comparison and Selection

| Module | Function | Description |
|--------|----------|-------------|
| `math_fp16_comparator` | a <=> b | Full comparison with flags |
| `math_fp16_max` | max(a, b) | Two-input maximum |
| `math_fp16_min` | min(a, b) | Two-input minimum |
| `math_fp16_max_tree_8` | max(a[7:0]) | 8-input maximum |
| `math_fp16_min_tree_8` | min(a[7:0]) | 8-input minimum |
| `math_fp16_clamp` | clamp(x, lo, hi) | Value clamping |

### Format Conversions

| Module | Conversion | Notes |
|--------|------------|-------|
| `math_fp16_to_bf16` | FP16 -> BF16 | Mantissa truncation, exponent adjustment |
| `math_fp16_to_fp32` | FP16 -> FP32 | Lossless upconversion |
| `math_fp16_to_fp8_e4m3` | FP16 -> FP8 E4M3 | For ML inference |
| `math_fp16_to_fp8_e5m2` | FP16 -> FP8 E5M2 | For ML training |

#### Conversion Notes

**FP16 to BF16:**
- Mantissa truncation: 10 bits -> 7 bits (may lose precision)
- Exponent mapping: bias 15 -> bias 127
- May overflow if FP16 value > BF16 max normal

**FP16 to FP32:**
- Lossless conversion (FP32 can represent all FP16 values)
- Simple exponent bias adjustment: 15 -> 127
- Mantissa padding: 10 bits -> 23 bits

## Usage Examples

### Mixed Precision Pipeline

```systemverilog
// FP16 computation with FP32 accumulator
logic [15:0] fp16_a, fp16_b, fp16_product;
logic [31:0] fp32_a, fp32_b, fp32_acc;

// Convert to FP32 for accumulation
math_fp16_to_fp32 u_cvt_a (.i_a(fp16_a), .ow_result(fp32_a), .ow_invalid());
math_fp16_to_fp32 u_cvt_b (.i_a(fp16_b), .ow_result(fp32_b), .ow_invalid());

// Compute in FP32 for precision
// ... FP32 MAC operation ...

// Apply FP16 activation
math_fp16_relu u_relu (.i_a(layer_output), .ow_result(activated));
```

### Comparison Operations

```systemverilog
logic [15:0] fp16_values [8];
logic [15:0] max_value, min_value;

math_fp16_max_tree_8 u_max (
    .i_values(fp16_values),
    .ow_max(max_value)
);

math_fp16_min_tree_8 u_min (
    .i_values(fp16_values),
    .ow_min(min_value)
);
```

## Special Values

| Value | Encoding | Notes |
|-------|----------|-------|
| +0 | 0x0000 | Positive zero |
| -0 | 0x8000 | Negative zero |
| +Inf | 0x7C00 | Positive infinity |
| -Inf | 0xFC00 | Negative infinity |
| NaN | 0x7E00 | Canonical quiet NaN |
| Max Normal | 0x7BFF | ~65504 |
| Min Normal | 0x0400 | ~6.1e-5 |
| Subnormal | Exp=0 | Flushed to zero (FTZ) |

## Auto-Generation

```bash
# Regenerate all FP16 modules
PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
```

## Related Documentation

- **[math_bf16_extended](math_bf16_extended.md)** - BF16 equivalent modules
- **[math_fp32_modules](math_fp32_modules.md)** - FP32 equivalent modules
- **[math_fp8_modules](math_fp8_modules.md)** - FP8 variants
- **[math_ieee754_modules](math_ieee754_modules.md)** - IEEE 754-2008 compliant arithmetic

## Navigation

- **[Back to RTLCommon Index](index.md)**
- **[Back to Main Documentation Index](../../index.md)**
