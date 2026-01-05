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

# BF16 Extended Modules

Extended BF16 (Brain Float 16) modules for AI/ML accelerators, including activation functions, mathematical operations, comparison/selection, and format conversions.

## Overview

Beyond the core BF16 arithmetic (adder, multiplier, FMA), this library provides a comprehensive set of modules for neural network inference and training. All modules follow IEEE 754-like conventions with Flush-to-Zero (FTZ) for subnormals.

**Key Features:**
- **Piecewise linear approximations** for transcendental functions
- **LUT-based implementations** for high accuracy where needed
- **Consistent interface** across all activation functions
- **NaN propagation** throughout all operations
- **Auto-generated** from Python generators for consistency

## Module Categories

### Activation Functions

Standard neural network activation functions with BF16 inputs and outputs.

| Module | Function | Description |
|--------|----------|-------------|
| `math_bf16_relu` | max(0, x) | Rectified Linear Unit - passes positive values, zeros negative |
| `math_bf16_leaky_relu` | max(0.01x, x) | Leaky ReLU - small gradient for negative values |
| `math_bf16_gelu` | x * Phi(x) | Gaussian Error Linear Unit - smooth approximation |
| `math_bf16_sigmoid` | 1/(1+exp(-x)) | Logistic function - output in (0, 1) |
| `math_bf16_tanh` | (exp(x)-exp(-x))/(exp(x)+exp(-x)) | Hyperbolic tangent - output in (-1, 1) |
| `math_bf16_silu` | x * sigmoid(x) | Sigmoid Linear Unit (Swish) |
| `math_bf16_softmax_8` | exp(xi)/sum(exp(xj)) | 8-input softmax normalization |

#### Common Interface Pattern

```systemverilog
module math_bf16_{activation} (
    input  logic [15:0] i_a,        // BF16 input
    output logic [15:0] ow_result   // BF16 output
);
```

#### Usage Example

```systemverilog
// Apply ReLU activation to layer output
math_bf16_relu u_relu (
    .i_a(layer_output),
    .ow_result(activated_output)
);

// Apply sigmoid for binary classification
math_bf16_sigmoid u_sigmoid (
    .i_a(logit),
    .ow_result(probability)
);
```

### Mathematical Operations

Extended math operations for neural network computations.

| Module | Function | Description |
|--------|----------|-------------|
| `math_bf16_exp2` | 2^x | Base-2 exponential (LUT + interpolation) |
| `math_bf16_log2` | log2(x) | Base-2 logarithm |
| `math_bf16_log2_scale` | log2(x) + scale | Scaled logarithm for normalization |
| `math_bf16_reciprocal` | 1/x | Full-precision reciprocal |
| `math_bf16_fast_reciprocal` | ~1/x | LUT-based fast approximation |
| `math_bf16_divider` | a/b | Full BF16 division |
| `math_bf16_goldschmidt_div` | a/b | Iterative Goldschmidt division |
| `math_bf16_newton_raphson_recip` | 1/x | Newton-Raphson iterative reciprocal |

#### Reciprocal/Division Modules

```systemverilog
// Fast reciprocal (single-cycle, LUT-based)
module math_bf16_fast_reciprocal #(
    parameter int LUT_DEPTH = 128    // 32, 64, or 128 entries
) (
    input  logic [15:0] i_a,
    output logic [15:0] ow_result,
    output logic        ow_overflow,
    output logic        ow_underflow,
    output logic        ow_invalid,
    output logic        ow_div_by_zero
);

// Goldschmidt division (iterative, higher accuracy)
module math_bf16_goldschmidt_div #(
    parameter int ITERATIONS = 2,     // 1 or 2 iterations
    parameter int PIPELINED = 1,      // 0=combinational, 1=pipelined
    parameter int LUT_DEPTH = 128     // Initial estimate LUT size
) (
    input  logic        i_clk,
    input  logic        i_rst_n,
    input  logic [15:0] i_a,          // Dividend
    input  logic [15:0] i_b,          // Divisor
    input  logic        i_valid,
    output logic [15:0] ow_result,
    output logic        ow_valid,
    output logic        ow_overflow,
    output logic        ow_underflow,
    output logic        ow_invalid,
    output logic        ow_div_by_zero
);
```

### Comparison and Selection

Modules for comparing and selecting BF16 values.

| Module | Function | Description |
|--------|----------|-------------|
| `math_bf16_comparator` | a <=> b | Full comparison with flags |
| `math_bf16_max` | max(a, b) | Two-input maximum |
| `math_bf16_min` | min(a, b) | Two-input minimum |
| `math_bf16_max_tree` | max(a[]) | N-input maximum tree |
| `math_bf16_max_tree_8` | max(a[7:0]) | 8-input maximum |
| `math_bf16_min_tree_8` | min(a[7:0]) | 8-input minimum |
| `math_bf16_clamp` | clamp(x, lo, hi) | Value clamping to range |

#### Comparator Interface

```systemverilog
module math_bf16_comparator (
    input  logic [15:0] i_a,
    input  logic [15:0] i_b,
    output logic        ow_eq,        // a == b
    output logic        ow_lt,        // a < b
    output logic        ow_gt,        // a > b
    output logic        ow_unordered  // NaN comparison
);
```

#### Max/Min Tree Usage

```systemverilog
// Find maximum across 8 values (e.g., for pooling)
logic [15:0] pool_inputs [8];
logic [15:0] pool_max;

math_bf16_max_tree_8 u_max_pool (
    .i_values(pool_inputs),
    .ow_max(pool_max)
);
```

### Format Conversions

Convert between BF16 and other floating-point formats.

| Module | Conversion | Description |
|--------|------------|-------------|
| `math_bf16_to_fp16` | BF16 -> FP16 | Requires mantissa rounding |
| `math_bf16_to_fp32` | BF16 -> FP32 | Lossless upconversion |
| `math_bf16_to_fp8_e4m3` | BF16 -> FP8 E4M3 | ML inference format |
| `math_bf16_to_fp8_e5m2` | BF16 -> FP8 E5M2 | ML training format |
| `math_bf16_to_int` | BF16 -> INT | Fixed-point conversion |
| `math_int_to_bf16` | INT -> BF16 | Integer to float conversion |
| `math_bf16_scale_to_int8` | BF16 -> INT8 | Quantization with scaling |

#### Conversion Interface Pattern

```systemverilog
module math_bf16_to_{format} (
    input  logic [15:0] i_a,          // BF16 input
    output logic [N:0]  ow_result,    // Target format output
    output logic        ow_overflow,  // Value too large
    output logic        ow_underflow, // Value too small (rounds to 0)
    output logic        ow_invalid    // NaN input
);
```

#### Quantization Example

```systemverilog
// Convert BF16 weights to INT8 for inference
logic [15:0] bf16_weight;
logic [7:0]  int8_weight;
logic [15:0] scale_factor;  // Pre-computed scale

math_bf16_scale_to_int8 u_quantize (
    .i_value(bf16_weight),
    .i_scale(scale_factor),
    .ow_result(int8_weight),
    .ow_overflow(quant_overflow),
    .ow_underflow()
);
```

## Special Value Handling

All modules follow consistent special value handling:

| Input | ReLU | Sigmoid | Max/Min | Converters |
|-------|------|---------|---------|------------|
| +0 | +0 | 0.5 | Compares as 0 | Format-specific 0 |
| -0 | +0 | 0.5 | Compares as 0 | Format-specific 0 |
| +Inf | +Inf | 1.0 | Largest | Overflow flag |
| -Inf | 0 | 0.0 | Smallest | Underflow flag |
| NaN | NaN | NaN | Propagates | Invalid flag |
| Subnormal | FTZ | FTZ | FTZ | FTZ |

## Implementation Notes

### Piecewise Linear Approximations

Transcendental functions (sigmoid, tanh, GELU) use piecewise linear approximation:

```
Sigmoid approximation regions:
  x <= -4:     sigmoid(x) = 0
  -4 < x < 0:  linear interpolation
  0 <= x < 4:  linear interpolation
  x >= 4:      sigmoid(x) = 1
```

This provides ~1-2% accuracy while maintaining single-cycle latency.

### LUT-Based Operations

For higher accuracy (exp2, log2, reciprocal), LUT + linear interpolation is used:

```systemverilog
// LUT stores function values at regular intervals
// Linear interpolation between adjacent entries
// Configurable LUT depth: 32, 64, or 128 entries
// Accuracy: ~0.1% for 128-entry LUT
```

## Auto-Generation

All modules are auto-generated for consistency:

```bash
# Regenerate all BF16 modules
PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
```

**Generator files:**
- `bin/rtl_generators/ieee754/fp_activations.py` - Activation functions
- `bin/rtl_generators/ieee754/fp_conversions.py` - Format converters
- `bin/rtl_generators/ieee754/fp_comparisons.py` - Comparison modules
- `bin/rtl_generators/ieee754/bf16_reciprocal.py` - Reciprocal/division

## Related Documentation

- **[math_bf16_multiplier](math_bf16_multiplier.md)** - Core BF16 multiplication
- **[math_bf16_adder](math_bf16_adder.md)** - Core BF16 addition
- **[math_bf16_fma](math_bf16_fma.md)** - Fused Multiply-Add
- **[math_fp16_modules](math_fp16_modules.md)** - FP16 equivalents
- **[math_fp8_modules](math_fp8_modules.md)** - FP8 E4M3/E5M2 modules

## Navigation

- **[Back to RTLCommon Index](index.md)**
- **[Back to Main Documentation Index](../../index.md)**
