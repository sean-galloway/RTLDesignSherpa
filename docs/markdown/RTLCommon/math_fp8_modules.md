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

# FP8 (8-bit Floating-Point) Modules

8-bit floating-point modules in both E4M3 and E5M2 formats for ML inference and training acceleration.

## Overview

FP8 formats provide extreme memory efficiency for neural network accelerators. Two variants are supported:
- **E4M3** - Higher precision, smaller range (inference-optimized)
- **E5M2** - Lower precision, larger range (training-friendly)

**FP8 E4M3 Format:**
```
[7]   = Sign bit
[6:3] = Exponent (4 bits, bias = 7)
[2:0] = Mantissa (3 bits)

Range: ~0.001953 to 448 (no infinity!)
Special: exp=15, mant=111 is NaN (not infinity)
Max normal: exp=15, mant=110 = 448
```

**FP8 E5M2 Format:**
```
[7]   = Sign bit
[6:2] = Exponent (5 bits, bias = 15)
[1:0] = Mantissa (2 bits)

Range: ~6e-8 to 57344 (has infinity)
Special: exp=31, mant=0 is Inf; mant!=0 is NaN
```

## Format Comparison

| Property | E4M3 | E5M2 | BF16 |
|----------|------|------|------|
| Total bits | 8 | 8 | 16 |
| Exponent bits | 4 | 5 | 8 |
| Mantissa bits | 3 | 2 | 7 |
| Max value | 448 | 57344 | ~3.4e38 |
| Min normal | 0.0156 | 6.1e-5 | ~1.2e-38 |
| Has infinity | No | Yes | Yes |
| Use case | Inference | Training | General |

## E4M3 Modules

### Core Arithmetic

| Module | Function | Description |
|--------|----------|-------------|
| `math_fp8_e4m3_adder` | a + b | FP8 E4M3 addition |
| `math_fp8_e4m3_multiplier` | a * b | FP8 E4M3 multiplication |
| `math_fp8_e4m3_fma` | a*b + c | Fused multiply-add |
| `math_fp8_e4m3_mantissa_mult` | Internal | Mantissa multiplication helper |
| `math_fp8_e4m3_exponent_adder` | Internal | Exponent computation helper |

#### Multiplier Interface

```systemverilog
module math_fp8_e4m3_multiplier (
    input  logic [7:0] i_a,
    input  logic [7:0] i_b,
    output logic [7:0] ow_result,
    output logic       ow_overflow,   // Saturates to max normal (448)
    output logic       ow_underflow,  // Flushes to zero
    output logic       ow_invalid     // NaN operation
);
```

**Note:** E4M3 has no infinity - overflow saturates to max normal value (0x7E = 448).

### Activation Functions

| Module | Function | Description |
|--------|----------|-------------|
| `math_fp8_e4m3_relu` | max(0, x) | ReLU activation |
| `math_fp8_e4m3_leaky_relu` | max(0.01x, x) | Leaky ReLU |
| `math_fp8_e4m3_gelu` | x * Phi(x) | GELU activation |
| `math_fp8_e4m3_sigmoid` | 1/(1+exp(-x)) | Sigmoid |
| `math_fp8_e4m3_tanh` | tanh(x) | Hyperbolic tangent |
| `math_fp8_e4m3_silu` | x * sigmoid(x) | SiLU/Swish |
| `math_fp8_e4m3_softmax_8` | softmax(x[7:0]) | 8-input softmax |

### Comparison and Selection

| Module | Function | Description |
|--------|----------|-------------|
| `math_fp8_e4m3_comparator` | a <=> b | Full comparison |
| `math_fp8_e4m3_max` | max(a, b) | Two-input max |
| `math_fp8_e4m3_min` | min(a, b) | Two-input min |
| `math_fp8_e4m3_max_tree_8` | max(a[7:0]) | 8-input max |
| `math_fp8_e4m3_min_tree_8` | min(a[7:0]) | 8-input min |
| `math_fp8_e4m3_clamp` | clamp(x, lo, hi) | Value clamping |

### Format Conversions

| Module | Conversion | Notes |
|--------|------------|-------|
| `math_fp8_e4m3_to_bf16` | E4M3 -> BF16 | Lossless upconversion |
| `math_fp8_e4m3_to_fp16` | E4M3 -> FP16 | Lossless upconversion |
| `math_fp8_e4m3_to_fp32` | E4M3 -> FP32 | Lossless upconversion |
| `math_fp8_e4m3_to_fp8_e5m2` | E4M3 -> E5M2 | May lose precision |

## E5M2 Modules

### Core Arithmetic

| Module | Function | Description |
|--------|----------|-------------|
| `math_fp8_e5m2_adder` | a + b | FP8 E5M2 addition |
| `math_fp8_e5m2_multiplier` | a * b | FP8 E5M2 multiplication |
| `math_fp8_e5m2_fma` | a*b + c | Fused multiply-add |
| `math_fp8_e5m2_mantissa_mult` | Internal | Mantissa multiplication helper |
| `math_fp8_e5m2_exponent_adder` | Internal | Exponent computation helper |

### Activation Functions

| Module | Function | Description |
|--------|----------|-------------|
| `math_fp8_e5m2_relu` | max(0, x) | ReLU activation |
| `math_fp8_e5m2_leaky_relu` | max(0.01x, x) | Leaky ReLU |
| `math_fp8_e5m2_gelu` | x * Phi(x) | GELU activation |
| `math_fp8_e5m2_sigmoid` | 1/(1+exp(-x)) | Sigmoid |
| `math_fp8_e5m2_tanh` | tanh(x) | Hyperbolic tangent |
| `math_fp8_e5m2_silu` | x * sigmoid(x) | SiLU/Swish |
| `math_fp8_e5m2_softmax_8` | softmax(x[7:0]) | 8-input softmax |

### Comparison and Selection

| Module | Function | Description |
|--------|----------|-------------|
| `math_fp8_e5m2_comparator` | a <=> b | Full comparison |
| `math_fp8_e5m2_max` | max(a, b) | Two-input max |
| `math_fp8_e5m2_min` | min(a, b) | Two-input min |
| `math_fp8_e5m2_max_tree_8` | max(a[7:0]) | 8-input max |
| `math_fp8_e5m2_min_tree_8` | min(a[7:0]) | 8-input min |
| `math_fp8_e5m2_clamp` | clamp(x, lo, hi) | Value clamping |

### Format Conversions

| Module | Conversion | Notes |
|--------|------------|-------|
| `math_fp8_e5m2_to_bf16` | E5M2 -> BF16 | Lossless upconversion |
| `math_fp8_e5m2_to_fp16` | E5M2 -> FP16 | Lossless upconversion |
| `math_fp8_e5m2_to_fp32` | E5M2 -> FP32 | Lossless upconversion |
| `math_fp8_e5m2_to_fp8_e4m3` | E5M2 -> E4M3 | May overflow/lose precision |

## Usage Examples

### Inference Pipeline (E4M3)

```systemverilog
// FP8 E4M3 inference - maximum memory efficiency
logic [7:0] weight, activation, product;

math_fp8_e4m3_multiplier u_mult (
    .i_a(weight),
    .i_b(activation),
    .ow_result(product),
    .ow_overflow(overflow),  // Saturates to 448
    .ow_underflow(),
    .ow_invalid()
);

// Apply activation
math_fp8_e4m3_relu u_relu (
    .i_a(product),
    .ow_result(activated)
);
```

### Mixed Precision Training

```systemverilog
// Forward pass in E5M2, upconvert for backward pass
logic [7:0]  fp8_activation;
logic [15:0] bf16_gradient;

// Upconvert for gradient computation
math_fp8_e5m2_to_bf16 u_cvt (
    .i_a(fp8_activation),
    .ow_result(bf16_activation),
    .ow_invalid()
);

// Compute gradients in BF16
// ... backward pass in BF16 ...
```

## Special Values

### E4M3 Special Values

| Value | Encoding | Notes |
|-------|----------|-------|
| +0 | 0x00 | Positive zero |
| -0 | 0x80 | Negative zero |
| Max Normal | 0x7E | 448 (exp=15, mant=6) |
| NaN | 0x7F | exp=15, mant=7 |
| No Infinity | - | Overflow saturates to 0x7E |

### E5M2 Special Values

| Value | Encoding | Notes |
|-------|----------|-------|
| +0 | 0x00 | Positive zero |
| -0 | 0x80 | Negative zero |
| +Inf | 0x7C | exp=31, mant=0 |
| -Inf | 0xFC | exp=31, mant=0 |
| NaN | 0x7E | exp=31, mant!=0 |

## Design Considerations

### E4M3 Overflow Handling

E4M3 has no infinity encoding. When multiplication would overflow:
- Result saturates to max normal (448 = 0x7E)
- `ow_overflow` flag asserts
- Sign is preserved

```systemverilog
// E4M3: Large values saturate instead of becoming infinity
// 400 * 2 = 800 -> saturates to 448
```

### Subnormal Handling

Both E4M3 and E5M2 use Flush-to-Zero (FTZ):
- Subnormal inputs treated as zero
- Results that would be subnormal flush to zero
- Simplifies hardware, matches AI accelerator conventions

## Auto-Generation

```bash
# Regenerate all FP8 modules
PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
```

**Generator files:**
- `bin/rtl_generators/ieee754/fp8_e4m3_multiplier.py`
- `bin/rtl_generators/ieee754/fp8_e5m2_multiplier.py`
- `bin/rtl_generators/ieee754/fp_activations.py`
- `bin/rtl_generators/ieee754/fp_conversions.py`

## Related Documentation

- **[math_bf16_extended](math_bf16_extended.md)** - BF16 modules
- **[math_fp16_modules](math_fp16_modules.md)** - FP16 modules
- **[math_fp32_modules](math_fp32_modules.md)** - FP32 modules
- **[math_ieee754_modules](math_ieee754_modules.md)** - IEEE 754-2008 arithmetic

## Navigation

- **[Back to RTLCommon Index](index.md)**
- **[Back to Main Documentation Index](../index.md)**
