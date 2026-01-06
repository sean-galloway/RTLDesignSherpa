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

# FP32 (Single Precision) Modules

IEEE 754 single-precision (FP32) floating-point modules for activation functions, comparison, and format conversion.

## Overview

FP32 (32-bit floating-point) provides full single-precision IEEE 754 representation. These modules support activation functions, comparisons, and downconversion to smaller formats.

**FP32 Format:**
```
[31]    = Sign bit
[30:23] = Exponent (8 bits, bias = 127)
[22:0]  = Mantissa (23 bits, implicit leading 1)

Range: ~1.2e-38 to ~3.4e38
Precision: ~0.00001% (7 decimal digits)
```

## Module Categories

### Activation Functions

| Module | Function | Description |
|--------|----------|-------------|
| `math_fp32_relu` | max(0, x) | Rectified Linear Unit |
| `math_fp32_leaky_relu` | max(0.01x, x) | Leaky ReLU |
| `math_fp32_gelu` | x * Phi(x) | Gaussian Error Linear Unit |
| `math_fp32_sigmoid` | 1/(1+exp(-x)) | Logistic function |
| `math_fp32_tanh` | tanh(x) | Hyperbolic tangent |
| `math_fp32_silu` | x * sigmoid(x) | SiLU/Swish activation |
| `math_fp32_softmax_8` | softmax(x[7:0]) | 8-input softmax |

#### Interface

```systemverilog
module math_fp32_{activation} (
    input  logic [31:0] i_a,        // FP32 input
    output logic [31:0] ow_result   // FP32 output
);
```

### Comparison and Selection

| Module | Function | Description |
|--------|----------|-------------|
| `math_fp32_comparator` | a <=> b | Full comparison with flags |
| `math_fp32_max` | max(a, b) | Two-input maximum |
| `math_fp32_min` | min(a, b) | Two-input minimum |
| `math_fp32_max_tree_8` | max(a[7:0]) | 8-input maximum |
| `math_fp32_min_tree_8` | min(a[7:0]) | 8-input minimum |
| `math_fp32_clamp` | clamp(x, lo, hi) | Value clamping |

### Format Conversions (Downconversion)

| Module | Conversion | Notes |
|--------|------------|-------|
| `math_fp32_to_bf16` | FP32 -> BF16 | Truncate mantissa (23->7 bits) |
| `math_fp32_to_fp16` | FP32 -> FP16 | Range check + rounding |
| `math_fp32_to_fp8_e4m3` | FP32 -> FP8 E4M3 | ML inference quantization |
| `math_fp32_to_fp8_e5m2` | FP32 -> FP8 E5M2 | ML training quantization |

#### Downconversion Notes

**FP32 to BF16:**
```systemverilog
module math_fp32_to_bf16 (
    input  logic [31:0] i_a,
    output logic [15:0] ow_result,
    output logic        ow_overflow,   // If exp > 254 in BF16
    output logic        ow_underflow,  // If exp < 1 (subnormal/zero)
    output logic        ow_invalid     // NaN input
);
```
- Same exponent range (8 bits), just truncate mantissa
- May lose precision in mantissa (23 -> 7 bits)
- RNE rounding applied

**FP32 to FP16:**
- Exponent range reduction: 8 bits -> 5 bits
- May overflow (FP32 value > 65504)
- May underflow (FP32 value < FP16 min subnormal)
- Mantissa rounding (23 -> 10 bits)

## Usage Examples

### Training Pipeline (FP32 Master)

```systemverilog
// FP32 forward pass with activation
logic [31:0] layer_input, layer_output, activated;

// FP32 computation (full precision for training)
// ... matrix multiply in FP32 ...

// FP32 activation
math_fp32_relu u_relu (
    .i_a(layer_output),
    .ow_result(activated)
);

// Convert to BF16 for storage/transfer
logic [15:0] bf16_result;
math_fp32_to_bf16 u_cvt (
    .i_a(activated),
    .ow_result(bf16_result),
    .ow_overflow(overflow_flag),
    .ow_underflow(),
    .ow_invalid()
);
```

### Quantization Pipeline

```systemverilog
// Quantize FP32 model weights to FP8 for inference
logic [31:0] fp32_weight;
logic [7:0]  fp8_weight;

math_fp32_to_fp8_e4m3 u_quantize (
    .i_a(fp32_weight),
    .ow_result(fp8_weight),
    .ow_overflow(quant_overflow),
    .ow_underflow(quant_underflow),
    .ow_invalid()
);
```

## Special Values

| Value | Encoding | Notes |
|-------|----------|-------|
| +0 | 0x00000000 | Positive zero |
| -0 | 0x80000000 | Negative zero |
| +Inf | 0x7F800000 | Positive infinity |
| -Inf | 0xFF800000 | Negative infinity |
| NaN | 0x7FC00000 | Canonical quiet NaN |
| Max Normal | 0x7F7FFFFF | ~3.4e38 |
| Min Normal | 0x00800000 | ~1.2e-38 |

## Auto-Generation

```bash
# Regenerate all FP32 modules
PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
```

## Related Documentation

- **[math_bf16_extended](math_bf16_extended.md)** - BF16 equivalent modules
- **[math_fp16_modules](math_fp16_modules.md)** - FP16 equivalent modules
- **[math_fp8_modules](math_fp8_modules.md)** - FP8 variants
- **[math_ieee754_modules](math_ieee754_modules.md)** - IEEE 754-2008 compliant arithmetic

## Navigation

- **[Back to RTLCommon Index](index.md)**
- **[Back to Main Documentation Index](../index.md)**
