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

# RTL Math Library

**Location:** `rtl/common/math_*.sv`
**Generators:** `bin/math_generate.py`, `bin/math_generate.sh`, `bin/rtl_generators/`
**Status:** Production Ready

---

## Overview

The `rtl/common/math_*` family is a ~170-module arithmetic library covering
integer add/subtract/multiply and IEEE-754-style floating-point (bf16, fp16,
fp32, fp8) arithmetic, comparison, conversion, and machine-learning activation
functions. The great majority of these modules are **code-generated** by the
Python framework under `bin/rtl_generators/`, so the library is best understood
by **operation** and, within each operation, by the **methodology** (algorithm)
used — rather than as a flat list of 170 files.

This document is the organizing map: each operation lists its methodologies, the
research each is based on, the module name pattern, and a link to the detailed
per-methodology doc. The floating-point cores are themselves built from the
integer methodologies below (Han-Carlson prefix adders for exponents, Dadda
trees for mantissa multiplies), so the two halves of the library share a
foundation.

**Naming convention:** width-parameterized generated instances carry the width
suffix (`_008`, `_016`, `_032`, …) and/or the format tag (`bf16`, `fp16`,
`fp32`, `fp8_e4m3`, `fp8_e5m2`, `ieee754_2008_*`). One methodology doc covers all
of its width/format instances.

---

## Integer Arithmetic

### Addition

| Methodology | Modules | Research | Detail |
|-------------|---------|----------|--------|
| Ripple-carry / full / half | `math_adder_full`, `math_adder_half`, `math_adder_full_nbit` | Classic ripple carry | [math_adder_full.md](math_adder_full.md), [math_adder_basic.md](math_adder_basic.md) |
| Carry-save (CSA) | `math_adder_carry_save_nbit` | Redundant carry-save form (used in multiplier trees) | [math_adder_carry_save.md](math_adder_carry_save.md) |
| Carry-lookahead | (see subtractor / adder-basic) | Weinberger & Smith, "A Logic for High-Speed Addition," NBS Circular 591 (1958) | [math_adder_pg_chain.md](math_adder_pg_chain.md) |
| **Brent-Kung** (parallel prefix) | `math_adder_brent_kung_{008,016,032}` + prefix cells (`_black`, `_gray`, `_pg`, `_bitwisepg`, `_grouppg_*`, `_sum`) | Brent, R.P. & Kung, H.T. (1982), "A Regular Layout for Parallel Adders," *IEEE Trans. Computers* C-31(3):260-264 | [math_adder_brent_kung.md](math_adder_brent_kung.md), [math_prefix_cell.md](math_prefix_cell.md) |
| **Han-Carlson** (parallel prefix) | `math_adder_han_carlson_{016,022,032,044,048,072}` | Han, T. & Carlson, D.A. (1987), "Fast area-efficient VLSI adders," *Proc. 8th IEEE Symp. Computer Arithmetic (ARITH)*:49-56 | [math_adder_han_carlson.md](math_adder_han_carlson.md) |
| Add/subtract | `math_addsub_full_nbit` | Two's-complement add/sub select | [math_addsub.md](math_addsub.md) |

**Parallel-prefix trade-off:** all three prefix adders compute the carry
network in O(log n) depth but differ in the area/wiring/fan-out balance —
Brent-Kung minimizes cells/wiring (more depth), Kogge-Stone minimizes depth
(most wiring), and Han-Carlson is the middle ground (a Kogge-Stone/Brent-Kung
hybrid). See the [prefix-cell](math_prefix_cell.md) and
[gray-cell](math_prefix_cell_gray.md) docs for the shared generate/propagate
building blocks.

### Subtraction

| Methodology | Modules | Detail |
|-------------|---------|--------|
| Ripple-carry / carry-lookahead / full / half | `math_subtractor_{full,half,full_nbit,ripple_carry,carry_lookahead}` | [math_subtractor.md](math_subtractor.md) |

### Multiplication

| Methodology | Modules | Research | Detail |
|-------------|---------|----------|--------|
| Basic cell / carry-save | `math_multiplier_basic_cell`, `math_multiplier_carry_save` | Shift-add partial-product cells | [math_multiplier_basic.md](math_multiplier_basic.md) |
| **Dadda tree** | `math_multiplier_dadda_tree_{008,016,032}`, `math_multiplier_dadda_4to2_{008,011,024}` | Dadda, L. (1965), "Some schemes for parallel multipliers," *Alta Frequenza* 34:349-356 | [math_multiplier_dadda_tree.md](math_multiplier_dadda_tree.md), [math_multiplier_dadda_4to2.md](math_multiplier_dadda_4to2.md) |
| **Wallace tree** | `math_multiplier_wallace_tree_{008,016,032}`, `math_multiplier_wallace_tree_csa_{008,016,032}` | Wallace, C.S. (1964), "A Suggestion for a Fast Multiplier," *IEEE Trans. Electronic Computers* EC-13(1):14-17 | [math_multiplier_wallace_tree.md](math_multiplier_wallace_tree.md) |

**Dadda vs Wallace:** both reduce the partial-product matrix to two rows in
O(log n) depth before a final carry-propagate add, but Dadda uses the *minimum*
number of (3:2) counters that still meets the height schedule (fewer gates,
slightly more wiring), while Wallace reduces as early/greedily as possible. The
`_csa` Wallace variant reduces with explicit carry-save adders. The `4to2`
variants use 4:2 compressors (see [math_compressor_4to2.md](math_compressor_4to2.md))
and are the building block the floating-point mantissa multipliers reuse.

---

## Floating-Point Arithmetic

IEEE-754-2008 single (fp32) and half (fp16) plus the ML-oriented narrow formats
bfloat16 (bf16) and 8-bit (fp8 `e4m3` / `e5m2`). Each format's core operators are
assembled from the integer methodologies above: the **exponent path** uses a
Han-Carlson prefix adder and the **mantissa multiply** uses a Dadda 4:2 tree.

### Formats

| Format | Modules tag | Notes |
|--------|-------------|-------|
| bfloat16 | `math_bf16_*` | 1-8-7; truncated fp32 range |
| IEEE fp16 | `math_fp16_*`, `math_ieee754_2008_fp16_*` | 1-5-10 |
| IEEE fp32 | `math_fp32_*`, `math_ieee754_2008_fp32_*` | 1-8-23 |
| fp8 E4M3 | `math_fp8_e4m3_*` | 1-4-3 |
| fp8 E5M2 | `math_fp8_e5m2_*` | 1-5-2 |

### Core operators (per format)

| Operation | Modules | Method | Detail |
|-----------|---------|--------|--------|
| Exponent add | `math_*_exponent_adder` | Han-Carlson prefix adder | [math_bf16_exponent_adder.md](math_bf16_exponent_adder.md) |
| Mantissa multiply | `math_*_mantissa_mult` | Dadda 4:2 tree | [math_bf16_mantissa_mult.md](math_bf16_mantissa_mult.md) |
| Add | `math_*_adder` | Align → add → normalize → round (IEEE-754 §5) | [math_bf16_adder.md](math_bf16_adder.md) |
| Multiply | `math_*_multiplier` | Exponent add + mantissa mult + normalize/round | [math_bf16_multiplier.md](math_bf16_multiplier.md) |
| Fused multiply-add | `math_*_fma` | Single-rounding a·b + c | [math_bf16_fma.md](math_bf16_fma.md) |

Detailed per-format coverage: [math_fp16_modules.md](math_fp16_modules.md),
[math_fp32_modules.md](math_fp32_modules.md), [math_fp8_modules.md](math_fp8_modules.md),
[math_ieee754_modules.md](math_ieee754_modules.md), and the bf16 set
([math_bf16_extended.md](math_bf16_extended.md)).

### Division & reciprocal

| Methodology | Modules | Research |
|-------------|---------|----------|
| Goldschmidt (multiplicative convergence) | `math_bf16_goldschmidt_div`, `math_bf16_divider` | Goldschmidt, R.E. (1964), "Applications of Division by Convergence," M.Sc. thesis, MIT |
| Newton-Raphson reciprocal | `math_bf16_newton_raphson_recip`, `math_bf16_reciprocal`, `math_bf16_fast_reciprocal` | Iterative `x_{n+1} = x_n(2 - a·x_n)` refinement of a seed |

### Conversion

`math_{src}_to_{dst}` — all bidirectional conversions among bf16 / fp16 / fp32 /
fp8_e4m3 / fp8_e5m2, plus integer bridges (`math_bf16_to_int`, `math_int_to_bf16`,
`math_bf16_scale_to_int8`). Each does exponent re-bias + mantissa round/truncate
with correct saturation/subnormal handling for the destination format.

### Comparison & range

`math_*_comparator`, `math_*_max`, `math_*_min`, `math_*_max_tree_8`,
`math_*_min_tree_8`, `math_*_clamp` — magnitude compare (sign/exp/mantissa
ordering), pairwise and 8-wide reduction trees, and clamp-to-range.

### Activation functions (ML)

`math_*_{relu, leaky_relu, gelu, silu, sigmoid, tanh, softmax_8}` plus the
transcendental helpers `math_bf16_{exp2, log2, log2_scale}`. These implement the
standard neural-network activations directly in each low-precision format
(piecewise / polynomial / LUT approximations sized to the format's mantissa),
so an accelerator can keep activations in bf16/fp8 without promoting to fp32.

---

## Generation Automation (`bin/`)

Almost every module above is emitted by a Python code-generator, so the RTL is
regenerated rather than hand-edited. Two entry points:

### Integer arithmetic — `bin/math_generate.py`

```bash
# one methodology + width per invocation
python bin/math_generate.py --type <brent_kung|dadda|wallace_fa|wallace_csa> \
                            --path <out_dir> --buswidth <N>
```

`bin/math_generate.sh` is the batch driver that sweeps the standard widths
(e.g. Brent-Kung at 8/16/32) into `math_outputs/`. The `--type` values map to the
methodologies: `brent_kung` (prefix adder), `dadda` / `wallace_fa` / `wallace_csa`
(the three multiplier reduction schemes). The emitters live in
`bin/rtl_generators/utils` (`write_bk` / `write_dadda` / `write_wallace`) and
`bin/rtl_generators/{adders,multipliers}/`.

### Floating-point — `bin/rtl_generators/ieee754/generate_all.py`

```bash
python bin/rtl_generators/ieee754/generate_all.py [output_directory]
```

Generates the full FP library: the shared integer cores (`han_carlson_adder`,
`dadda_4to2_multiplier`) followed by each format's `{mantissa_mult,
exponent_adder, multiplier, adder, fma}` and all cross-format conversions. The
bf16 set has its own `bin/rtl_generators/bf16/generate_all.py`, and the
activation / comparison / conversion families are emitted by
`fp_activations.py`, `fp_comparisons.py`, and `fp_conversions.py`.

### The emitter framework — `bin/rtl_generators/`

| Path | Role |
|------|------|
| `verilog/module.py`, `param.py`, `signal.py`, `verilog_parser.py` | Structured Verilog emission (ports, params, signals) — the backend every generator writes through |
| `utils/utils.py` | Shared helpers (`write_bk`, `write_dadda`, `write_wallace`, formatting) |
| `adders/`, `multipliers/` | Integer methodology generators (Brent-Kung, Dadda, Wallace) |
| `ieee754/`, `bf16/` | Per-format FP operator generators + `generate_all.py` |
| `ecc/`, `amba/` | Other generated families (not part of `math_*`) |
| `unittests/` | Generator self-tests |

### Regeneration rule

These are generated files. Per the repo's Critical Rule #0, when a **generator**
changes you must delete and regenerate **all** affected outputs (not a single
width/format) and re-run the tests, because widths/cells share interfaces and a
partial regen creates silent interface mismatches. Do not hand-edit a
`math_*.sv` that a generator owns — change the generator and regenerate.

---

## Research References

- Brent, R.P. & Kung, H.T. (1982). "A Regular Layout for Parallel Adders." *IEEE Transactions on Computers*, C-31(3), 260-264.
- Han, T. & Carlson, D.A. (1987). "Fast area-efficient VLSI adders." *Proc. 8th IEEE Symposium on Computer Arithmetic (ARITH-8)*, 49-56.
- Kogge, P.M. & Stone, H.S. (1973). "A Parallel Algorithm for the Efficient Solution of a General Class of Recurrence Equations." *IEEE Transactions on Computers*, C-22(8), 786-793.
- Dadda, L. (1965). "Some schemes for parallel multipliers." *Alta Frequenza*, 34, 349-356.
- Wallace, C.S. (1964). "A Suggestion for a Fast Multiplier." *IEEE Transactions on Electronic Computers*, EC-13(1), 14-17.
- Weinberger, A. & Smith, J.L. (1958). "A Logic for High-Speed Addition." *National Bureau of Standards Circular 591*, 3-12.
- Goldschmidt, R.E. (1964). "Applications of Division by Convergence." M.Sc. thesis, MIT.
- IEEE Std 754-2008, *IEEE Standard for Floating-Point Arithmetic*.

---

## Related Documentation

- Prefix cells: [math_prefix_cell.md](math_prefix_cell.md) · [math_prefix_cell_gray.md](math_prefix_cell_gray.md)
- Multipliers: [dadda_tree](math_multiplier_dadda_tree.md) · [dadda_4to2](math_multiplier_dadda_4to2.md) · [wallace_tree](math_multiplier_wallace_tree.md) · [basic](math_multiplier_basic.md) · [compressor_4to2](math_compressor_4to2.md)
- Subtraction: [math_subtractor.md](math_subtractor.md)
- Floating-point: [bf16 extended](math_bf16_extended.md) · [fp16](math_fp16_modules.md) · [fp32](math_fp32_modules.md) · [fp8](math_fp8_modules.md) · [ieee754](math_ieee754_modules.md)

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to RTLCommon Index](index.md)
