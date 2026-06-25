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

# Floating-Point Math — Class Overview

**Category:** Arithmetic primitives (FP)
**Scope:** `rtl/common/math_bf16_*.sv`, `math_fp16_*.sv`, `math_fp32_*.sv`, `math_fp8_e4m3_*.sv`, `math_fp8_e5m2_*.sv`, `math_ieee754_2008_*.sv`, `math_int_to_bf16.sv` (~120 modules)
**Status:** Production-ready

---

## What this is

A neural-network-oriented floating-point library covering BF16, FP16, FP32, and both FP8 formats (E4M3, E5M2). For each format the library provides the core arithmetic (add, multiply, FMA, comparator, min/max, divider/reciprocal where applicable), activation functions used in inference (ReLU, leaky ReLU, GELU, SiLU, sigmoid, tanh, softmax), tree-reduction helpers (`*_max_tree`, `*_min_tree`), and the cross-format converters. A separate `math_ieee754_2008_*` family provides full IEEE-754-2008 compliant FP16/FP32 arithmetic with proper subnormal handling for use cases that need strict compliance.

## Why use this class

These modules are the arithmetic substrate for ML accelerators: low-precision arithmetic for matmul, BF16/FP32 mixed-precision FMAs for training-style accumulation, piecewise-linear activations for inference, and the cross-format converters needed to glue mixed-precision pipelines together. The non-IEEE variants use Flush-to-Zero (FTZ) on subnormals for cleaner area/timing; the `ieee754_2008` variants are there when full compliance matters.

## Members

### BF16 (`math_bf16_*`) — primary AI/ML format

- **Core arithmetic:** [`math_bf16_adder.sv`](../../../rtl/common/math_bf16_adder.sv), [`math_bf16_multiplier.sv`](../../../rtl/common/math_bf16_multiplier.sv), [`math_bf16_fma.sv`](../../../rtl/common/math_bf16_fma.sv) (BF16×BF16 + FP32 → FP32), [`math_bf16_mantissa_mult.sv`](../../../rtl/common/math_bf16_mantissa_mult.sv), [`math_bf16_exponent_adder.sv`](../../../rtl/common/math_bf16_exponent_adder.sv)
- **Division / reciprocal:** [`math_bf16_divider.sv`](../../../rtl/common/math_bf16_divider.sv), [`math_bf16_reciprocal.sv`](../../../rtl/common/math_bf16_reciprocal.sv), [`math_bf16_fast_reciprocal.sv`](../../../rtl/common/math_bf16_fast_reciprocal.sv), [`math_bf16_newton_raphson_recip.sv`](../../../rtl/common/math_bf16_newton_raphson_recip.sv), [`math_bf16_goldschmidt_div.sv`](../../../rtl/common/math_bf16_goldschmidt_div.sv)
- **Compare / min / max:** [`math_bf16_comparator.sv`](../../../rtl/common/math_bf16_comparator.sv), `math_bf16_min.sv`, `math_bf16_max.sv`, `math_bf16_min_tree[_8].sv`, `math_bf16_max_tree[_8].sv`, [`math_bf16_clamp.sv`](../../../rtl/common/math_bf16_clamp.sv)
- **Activations / transcendentals:** `math_bf16_relu.sv`, `math_bf16_leaky_relu.sv`, [`math_bf16_gelu.sv`](../../../rtl/common/math_bf16_gelu.sv), [`math_bf16_silu.sv`](../../../rtl/common/math_bf16_silu.sv), [`math_bf16_sigmoid.sv`](../../../rtl/common/math_bf16_sigmoid.sv), [`math_bf16_tanh.sv`](../../../rtl/common/math_bf16_tanh.sv), `math_bf16_softmax_8.sv`, [`math_bf16_exp2.sv`](../../../rtl/common/math_bf16_exp2.sv), [`math_bf16_log2.sv`](../../../rtl/common/math_bf16_log2.sv), `math_bf16_log2_scale.sv`
- **Converters:** `math_bf16_to_fp16.sv`, `math_bf16_to_fp32.sv`, `math_bf16_to_fp8_e4m3.sv`, `math_bf16_to_fp8_e5m2.sv`, `math_bf16_to_int.sv`, `math_bf16_scale_to_int8.sv`, [`math_int_to_bf16.sv`](../../../rtl/common/math_int_to_bf16.sv)

### FP16 (`math_fp16_*`)

Compare / min / max / clamp, activations (ReLU, leaky ReLU, GELU, SiLU, sigmoid, tanh, softmax_8), tree reductions, and converters to/from BF16, FP32, FP8 E4M3/E5M2.

### FP32 (`math_fp32_*`)

Same shape as FP16: compare/min/max/clamp, activation set, tree reductions, and converters to BF16, FP16, FP8 E4M3/E5M2. No native add/multiply in this set — use the `ieee754_2008_fp32_*` family for FP32 arithmetic.

### FP8 E4M3 (`math_fp8_e4m3_*`) — inference-optimized

Full arithmetic kit: adder, multiplier, FMA, mantissa multiplier, exponent adder, comparator, min/max (+ tree_8), clamp, activations (ReLU, leaky, GELU, SiLU, sigmoid, tanh, softmax_8), and converters to BF16, FP16, FP32, FP8 E5M2.

### FP8 E5M2 (`math_fp8_e5m2_*`) — training-friendly

Identical surface to E4M3 with E5M2 format internally.

### IEEE-754-2008 compliant (`math_ieee754_2008_*`) — strict compliance

| Module | Role |
|---|---|
| [`math_ieee754_2008_fp16_adder.sv`](../../../rtl/common/math_ieee754_2008_fp16_adder.sv) | IEEE-compliant FP16 add (proper subnormals) |
| [`math_ieee754_2008_fp16_multiplier.sv`](../../../rtl/common/math_ieee754_2008_fp16_multiplier.sv) / [`_mantissa_mult.sv`](../../../rtl/common/math_ieee754_2008_fp16_mantissa_mult.sv) / [`_exponent_adder.sv`](../../../rtl/common/math_ieee754_2008_fp16_exponent_adder.sv) / [`_fma.sv`](../../../rtl/common/math_ieee754_2008_fp16_fma.sv) | FP16 multiply, mantissa/exponent paths, FMA |
| `math_ieee754_2008_fp32_*` | Same set for FP32 |

## Picking guide

For AI/ML at training-style precision, the BF16 family is the default. For inference at smaller footprint use FP8 (E4M3 inference, E5M2 wider-dynamic-range / training). FP16 modules cover activations and conversion but lean on `ieee754_2008_fp16_*` for arithmetic. FP32 in this directory is mainly the activation / conversion set — use `ieee754_2008_fp32_*` if you need strict-IEEE FP32 add/multiply/FMA. For mixed-precision training, `math_bf16_fma` (BF16×BF16+FP32→FP32) is the canonical block.

## Tests

[`val/common/`](../../../val/common/) — pytest + CocoTB suite. Naming: `test_math_bf16_*.py`, `test_math_fp16_*.py`, `test_math_fp32_*.py`, `test_math_fp8_*.py`, `test_math_ieee754_*.py`.

## Full per-module specs

[`docs/markdown/RTLCommon/`](../../markdown/RTLCommon/) — `math_bf16_*.md`, `math_fp16_modules.md`, `math_fp32_modules.md`, `math_fp8_modules.md`, `math_ieee754_modules.md`. Use those for parameter descriptions, port lists, and accuracy notes.

## Source

[`rtl/common/`](../../../rtl/common/) (`math_bf16_*.sv`, `math_fp16_*.sv`, `math_fp32_*.sv`, `math_fp8_e4m3_*.sv`, `math_fp8_e5m2_*.sv`, `math_ieee754_2008_*.sv`, `math_int_to_bf16.sv`)

---

## Navigation

- **[← Back to RTL Design Sherpa README](../../../README.md)**
- **[← Browse by Class index](../../../README.md#browse-by-class)**
- **[Main Documentation Index](../../DOCUMENTATION_INDEX.md)**
- **[Common Library per-module specs](../../markdown/RTLCommon/index.md)**
