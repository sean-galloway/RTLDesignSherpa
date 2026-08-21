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

# rtl-math module index

**RTL:** `rtl/math/` (172 modules)
**Tests:** `val/math/`
**Common building blocks:** [rtl-common](../rtl-common/index.md)

The complete `math_*` arithmetic library: adders, subtractors, multipliers,
compressors, prefix cells, and the BF16 / FP8 / FP16 / FP32 / IEEE-754
floating-point modules — every family, with the files that make it up.

## Start here

This page is the catalogue, not the guide. Read the **[Math Library
overview](math_library.md)** first: it organizes the whole `math_*` family by
operation → methodology — Brent-Kung / Han-Carlson adders, Dadda / Wallace
multipliers, IEEE-754 fp32/fp16/bf16/fp8 operators, conversions, and
activations — each with its research reference and a link to the detailed doc
below, plus the `bin/` code-generation automation. Come back here when you
need the exact file list.

## Module categories

### Basic arithmetic

- **[math_adder_basic](math_adder_basic.md)** — single-bit adders (full and half adder)
  - Includes: `math_adder_full.sv` ([dedicated page](math_adder_full.md)), `math_adder_half.sv`, `math_adder_full_nbit.sv`
- **[math_adder_ripple_carry](math_adder_ripple_carry.md)** — multi-bit ripple carry adder
- **[math_adder_pg_chain](math_adder_pg_chain.md)** — fast carry lookahead adder
- **[math_adder_carry_save](math_adder_carry_save.md)** — carry-save adder for multiple operands
  - Includes: `math_adder_carry_save.sv`, `math_adder_carry_save_nbit.sv`

### Advanced adders

- **[math_adder_brent_kung](math_adder_brent_kung.md)** — Brent-Kung parallel prefix adder family (8/16/32/64-bit)
  - Includes: `math_adder_brent_kung_008.sv`, `math_adder_brent_kung_016.sv`, `math_adder_brent_kung_032.sv`, `math_adder_brent_kung_064.sv`
  - Sub-modules: `math_adder_brent_kung_pg.sv`, `math_adder_brent_kung_black.sv`, `math_adder_brent_kung_gray.sv`, `math_adder_brent_kung_bitwisepg.sv`, `math_adder_brent_kung_grouppg_*.sv`, `math_adder_brent_kung_sum.sv`
- **[math_adder_han_carlson](math_adder_han_carlson.md)** — Han-Carlson hybrid parallel prefix adder family (16/22/32/44/48/72-bit)
  - Includes: `math_adder_han_carlson_016.sv`, `math_adder_han_carlson_022.sv`, `math_adder_han_carlson_032.sv`, `math_adder_han_carlson_044.sv`, `math_adder_han_carlson_048.sv`, `math_adder_han_carlson_072.sv`
  - Building blocks: `math_prefix_cell.sv`, `math_prefix_cell_gray.sv`
- **[math_addsub](math_addsub.md)** — combined adder/subtractor
  - Includes: `math_addsub_full_nbit.sv`

### Subtraction

- **[math_subtractor](math_subtractor.md)** — subtractor family (single-bit and multi-bit)
  - Includes: `math_subtractor_full.sv`, `math_subtractor_half.sv`, `math_subtractor_full_nbit.sv`, `math_subtractor_ripple_carry.sv`, `math_subtractor_carry_lookahead.sv`

### Multiplication

- **[math_multiplier_wallace_tree](math_multiplier_wallace_tree.md)** — Wallace tree multiplier family (8/16/32-bit)
  - Includes: `math_multiplier_wallace_tree_008.sv`, `math_multiplier_wallace_tree_016.sv`, `math_multiplier_wallace_tree_032.sv`
  - CSA variants: `math_multiplier_wallace_tree_csa_008.sv`, `math_multiplier_wallace_tree_csa_016.sv`, `math_multiplier_wallace_tree_csa_032.sv`
- **[math_multiplier_dadda_tree](math_multiplier_dadda_tree.md)** — Dadda tree multiplier family (8/16/32-bit)
  - Includes: `math_multiplier_dadda_tree_008.sv`, `math_multiplier_dadda_tree_016.sv`, `math_multiplier_dadda_tree_032.sv`
- **[math_multiplier_dadda_4to2](math_multiplier_dadda_4to2.md)** — Dadda tree multiplier with 4:2 compressors (8/11/24-bit)
  - Includes: `math_multiplier_dadda_4to2_008.sv` (BF16), `math_multiplier_dadda_4to2_011.sv` (FP16), `math_multiplier_dadda_4to2_024.sv` (FP32)
  - Building blocks: `math_compressor_4to2.sv`
- **[math_multiplier_basic](math_multiplier_basic.md)** — basic multiplier components
  - Includes: `math_multiplier_basic_cell.sv`, `math_multiplier_carry_save.sv`

### BF16 floating-point arithmetic

- **[math_bf16_adder](math_bf16_adder.md)** — pipelined BF16 adder with configurable latency
  - Includes: `math_bf16_adder.sv`
  - Dependencies: `shifter_barrel.sv`, `count_leading_zeros.sv`
- **[math_bf16_multiplier](math_bf16_multiplier.md)** — complete BF16 multiplier with IEEE 754 compliance
  - Includes: `math_bf16_multiplier.sv`
  - Sub-modules: `math_bf16_mantissa_mult.sv`, `math_bf16_exponent_adder.sv`
- **[math_bf16_mantissa_mult](math_bf16_mantissa_mult.md)** — BF16 mantissa multiplier with normalization detection
  - Includes: `math_bf16_mantissa_mult.sv`
- **[math_bf16_exponent_adder](math_bf16_exponent_adder.md)** — BF16 exponent computation with overflow/underflow detection
  - Includes: `math_bf16_exponent_adder.sv`
- **[math_bf16_fma](math_bf16_fma.md)** — BF16 Fused Multiply-Add with FP32 accumulator for AI training
  - Includes: `math_bf16_fma.sv`
- **[math_bf16_extended](math_bf16_extended.md)** — extended BF16 modules (29 modules)
  - Activation functions: `relu`, `leaky_relu`, `gelu`, `sigmoid`, `tanh`, `silu`, `softmax_8`
  - Math operations: `exp2`, `log2`, `log2_scale`, `reciprocal`, `fast_reciprocal`, `divider`, `goldschmidt_div`, `newton_raphson_recip`
  - Comparison/Selection: `comparator`, `clamp`, `min`, `max`, `min_tree_8`, `max_tree`, `max_tree_8`
  - Format conversions: `to_fp16`, `to_fp32`, `to_fp8_e4m3`, `to_fp8_e5m2`, `to_int`, `int_to_bf16`, `scale_to_int8`

### FP16 (half-precision) floating-point

- **[math_fp16_modules](math_fp16_modules.md)** — FP16 module collection (17 modules)
  - Activation functions: `relu`, `leaky_relu`, `gelu`, `sigmoid`, `tanh`, `silu`, `softmax_8`
  - Comparison/Selection: `comparator`, `clamp`, `min`, `max`, `min_tree_8`, `max_tree_8`
  - Format conversions: `to_bf16`, `to_fp32`, `to_fp8_e4m3`, `to_fp8_e5m2`

### FP32 (single-precision) floating-point

- **[math_fp32_modules](math_fp32_modules.md)** — FP32 module collection (17 modules)
  - Activation functions: `relu`, `leaky_relu`, `gelu`, `sigmoid`, `tanh`, `silu`, `softmax_8`
  - Comparison/Selection: `comparator`, `clamp`, `min`, `max`, `min_tree_8`, `max_tree_8`
  - Format conversions: `to_bf16`, `to_fp16`, `to_fp8_e4m3`, `to_fp8_e5m2`

### FP8 (8-bit floating-point)

- **[math_fp8_modules](math_fp8_modules.md)** — FP8 E4M3 and E5M2 module collection (44 modules)
  - E4M3 (inference): `adder`, `multiplier`, `fma`, activations, comparisons, conversions
  - E5M2 (training): `adder`, `multiplier`, `fma`, activations, comparisons, conversions
  - Format conversions between E4M3, E5M2, BF16, FP16, FP32

### IEEE 754-2008 compliant arithmetic

- **[math_ieee754_modules](math_ieee754_modules.md)** — IEEE 754-2008 arithmetic (10 modules; multipliers sweep-verified to spec incl. RNE and after-rounding underflow -- the adder/FMA underflow corner is unaudited, see rtl/math/CLAUDE.md)
  - FP16: `adder`, `multiplier`, `fma`, `mantissa_mult`, `exponent_adder`
  - FP32: `adder`, `multiplier`, `fma`, `mantissa_mult`, `exponent_adder`
  - Features: proper subnormal handling, pipelined options, full status flags

### Compressors and prefix cells

- **[math_compressor_4to2](math_compressor_4to2.md)** — 4:2 compressor for fast parallel reduction
- **[math_mod_3_compress](math_mod_3_compress.md)** — combinational `X - (X mod 3)` carry-save rounding (monbus record packing)
- **[math_prefix_cell](math_prefix_cell.md)** — black cell for parallel prefix adders
  - Includes: `math_prefix_cell.sv`
- **[math_prefix_cell_gray](math_prefix_cell_gray.md)** — gray cell for parallel prefix adders (area-optimized)
  - Includes: `math_prefix_cell_gray.sv`

## Related

- [rtl-common index](../rtl-common/index.md) — counters, FIFOs, arbiters, CDC,
  data integrity
- [Documentation index](../../DOCUMENTATION_INDEX.md)
