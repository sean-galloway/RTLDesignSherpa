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

# Integer Math — Class Overview

**Category:** Arithmetic primitives
**Scope:** `rtl/common/math_adder_*.sv`, `math_subtractor_*.sv`, `math_addsub_*.sv`, `math_multiplier_*.sv`, `math_compressor_*.sv`, `math_prefix_cell*.sv`, plus `leading_one_trailing_one.sv`, `bin2gray.sv`, `gray2bin.sv` (~40 modules)
**Status:** Production-ready

---

## What this is

Integer arithmetic building blocks: full/half adders and subtractors, ripple-carry through to parallel-prefix adders (Brent-Kung, Han-Carlson, Kogge-Stone, carry-lookahead, carry-save), Wallace and Dadda multiplier trees with 4:2 compressors, the shared prefix cells used inside the parallel-prefix adders, and the small bit-manipulation helpers (`leading_one_trailing_one`, `bin2gray`, `gray2bin`) that pair with arithmetic for normalization and Gray pointers.

## Why use this class

When you need an adder or multiplier, the question is never "can I build one?" — it's "which topology hits my timing/area target?" This class spans the full PPA curve, from area-optimal ripple-carry up to log-depth parallel-prefix trees and parallel-reduction multipliers. The leaf cells (full adder, prefix cell, 4:2 compressor) are also exposed so you can compose new structures.

## Members

### Leaf cells

| Module | Role |
|---|---|
| [`math_adder_half.sv`](../../../rtl/common/math_adder_half.sv) / [`_full.sv`](../../../rtl/common/math_adder_full.sv) | Single-bit half / full adder |
| [`math_subtractor_half.sv`](../../../rtl/common/math_subtractor_half.sv) / [`_full.sv`](../../../rtl/common/math_subtractor_full.sv) | Single-bit half / full subtractor |
| [`math_prefix_cell.sv`](../../../rtl/common/math_prefix_cell.sv) | Parallel-prefix "black" cell (group G + P) |
| [`math_prefix_cell_gray.sv`](../../../rtl/common/math_prefix_cell_gray.sv) | Reduced-area "gray" cell (group G only) |
| [`math_compressor_4to2.sv`](../../../rtl/common/math_compressor_4to2.sv) | 4:2 compressor for Wallace/Dadda reduction trees |

### Adders (n-bit)

| Module | Role | Pick when |
|---|---|---|
| [`math_adder_ripple_carry.sv`](../../../rtl/common/math_adder_ripple_carry.sv) | O(N) ripple carry | Area-critical, low frequency |
| [`math_adder_carry_lookahead.sv`](../../../rtl/common/math_adder_carry_lookahead.sv) | CLA, P/G | 4–16 bits, balanced PPA |
| [`math_adder_carry_save.sv`](../../../rtl/common/math_adder_carry_save.sv) / [`_nbit`](../../../rtl/common/math_adder_carry_save_nbit.sv) | 3:2 compressor, constant depth | Multi-operand sums, inside multipliers |
| [`math_adder_brent_kung_{008,016,032}.sv`](../../../rtl/common/) | Brent-Kung parallel-prefix | Log-depth adder, area-aware |
| [`math_adder_han_carlson_{016,022,032,044,048,072}.sv`](../../../rtl/common/) | Han-Carlson sparsity-2 prefix | Log-depth adder, BF16 mantissa (48b) |
| [`math_adder_kogge_stone_nbit.sv`](../../../rtl/common/math_adder_kogge_stone_nbit.sv) | Kogge-Stone-inspired | Generic-width parameterizable variant |
| [`math_adder_full_nbit.sv`](../../../rtl/common/math_adder_full_nbit.sv) | N-bit chained full adder | Simplest n-bit wrapper |
| [`math_addsub_full_nbit.sv`](../../../rtl/common/math_addsub_full_nbit.sv) | Shared add/sub via XOR + carry-in | Need both ops in one unit |

### Subtractors

| Module | Role |
|---|---|
| [`math_subtractor_ripple_carry.sv`](../../../rtl/common/math_subtractor_ripple_carry.sv) / [`_full_nbit.sv`](../../../rtl/common/math_subtractor_full_nbit.sv) / [`_carry_lookahead.sv`](../../../rtl/common/math_subtractor_carry_lookahead.sv) | N-bit subtractors mirroring the adder family |

### Multipliers (8/16/32-bit families)

| Module | Role |
|---|---|
| [`math_multiplier_basic_cell.sv`](../../../rtl/common/math_multiplier_basic_cell.sv) / [`_carry_save.sv`](../../../rtl/common/math_multiplier_carry_save.sv) | Array-style baseline multiplier |
| [`math_multiplier_wallace_tree_{008,016,032}.sv`](../../../rtl/common/) (+`_csa_*`) | Wallace tree — maximal parallel reduction |
| [`math_multiplier_dadda_tree_{008,016,032}.sv`](../../../rtl/common/) | Dadda tree — scheduled reduction, smaller |
| [`math_multiplier_dadda_4to2_{008,011,024}.sv`](../../../rtl/common/) | Dadda variant using 4:2 compressors |

### Bit helpers (paired with arithmetic)

| Module | Role |
|---|---|
| [`leading_one_trailing_one.sv`](../../../rtl/common/leading_one_trailing_one.sv) | First/last set-bit position + one-hot |
| [`bin2gray.sv`](../../../rtl/common/bin2gray.sv) / [`gray2bin.sv`](../../../rtl/common/gray2bin.sv) | Combinational binary↔Gray conversion |

## Picking guide

Adders: ripple-carry for tiny widths or area-bound paths, CLA up to ~16 bits, Brent-Kung or Han-Carlson for log-depth at 16/32/48+ bits (Han-Carlson is the BF16 mantissa choice). Use carry-save when summing more than two operands or inside a multiplier reduction tree. Multipliers: pick Dadda over Wallace when area matters; pick `_csa_*` variants when you want the carry-save flavor of Wallace. Compose your own with `math_prefix_cell*` and `math_compressor_4to2` as leaves.

## Tests

[`val/common/`](../../../val/common/) — pytest + CocoTB suite. Naming: `test_math_adder_*.py`, `test_math_multiplier_*.py`, `test_math_subtractor_*.py`, `test_leading_one_trailing_one.py`, `test_bin2gray.py`, `test_gray2bin.py`.

## Full per-module specs

[`docs/markdown/RTLCommon/`](../../markdown/RTLCommon/) — `math_adder_*`, `math_subtractor.md`, `math_multiplier_*`, `math_compressor_4to2.md`, `math_prefix_cell*.md`. Use those for parameter descriptions, port lists, and timing/area data.

## Source

[`rtl/common/`](../../../rtl/common/) (`math_adder_*.sv`, `math_subtractor_*.sv`, `math_addsub_*.sv`, `math_multiplier_*.sv`, `math_compressor_*.sv`, `math_prefix_cell*.sv`, `leading_one_trailing_one.sv`, `bin2gray.sv`, `gray2bin.sv`)

---

## Navigation

- **[← Back to RTL Design Sherpa README](../../../README.md)**
- **[← Browse by Class index](../../../README.md#browse-by-class)**
- **[Main Documentation Index](../../DOCUMENTATION_INDEX.md)**
- **[Common Library per-module specs](../../markdown/RTLCommon/index.md)**
