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

# Arithmetic

**RTL:** `rtl/math/` (171 modules)
**Filelists:** `rtl/math/filelists/` (38) — lint the whole area with `math_all.f`
**Tests:** `val/math/` (119)

Everything that computes a number lives here: integer add, subtract and
multiply, and the IEEE-754-style floating-point operators in bf16, fp16, fp32
and the two fp8 flavours. The library was split out of `rtl/common/` because it
had outgrown it — 171 of the repository's modules are arithmetic, and mixing
them with counters and FIFOs made both harder to navigate. If a doc still says
`rtl/common/math_*`, it is stale.

**Full catalogue:** [index.md](index.md)

## Start here

[The Math Library map](math_library.md) is the document to read first. A flat
list of 171 files is not navigable, so that page organizes the library the way
you would actually search it: by **operation**, and within each operation by
**methodology** — the algorithm and the paper it comes from. Brent-Kung against
Han-Carlson against Kogge-Stone for prefix addition; Dadda against Wallace for
partial-product reduction. Each entry names its research reference and links to
the per-methodology page.

| Jump to | Covers |
|---------|--------|
| [Integer arithmetic](math_library.md#integer-arithmetic) | Adders, subtractors, multipliers, the 4:2 compressor and prefix cells |
| [Floating-point arithmetic](math_library.md#floating-point-arithmetic) | Formats, core operators, division, conversion, comparison, activations |
| [Generation automation](math_library.md#generation-automation-bin) | The Python emitters that produce most of this RTL |
| [Research references](math_library.md#research-references) | The papers each methodology implements |

## How the library is shaped

Two things about this area differ from every other area in the repository, and
both change how you work in it.

**Most of it is generated.** 118 of the 171 modules carry a generator banner.
They come from `bin/math_generate.py` (integer) and
`bin/rtl_generators/ieee754/generate_all.py` (floating point), built on the
emitter framework in `bin/rtl_generators/`. Editing a generated `.sv` by hand
is not a fix — it is a change that the next regeneration silently discards.
Change the generator, then **delete every generated file and regenerate the
whole set**, because partial regeneration produces port and width mismatches
that fail as confusing simulation errors rather than as compile errors. This is
CRITICAL RULE #0 in the repository guide, and arithmetic is where it bites
hardest: a mantissa-width change touches dozens of files at once.

**One page covers many modules.** Width-parameterized instances carry a suffix
(`_008`, `_016`, `_032`) and format variants carry a tag (`bf16`, `fp16`,
`fp32`, `fp8_e4m3`, `fp8_e5m2`). A single methodology page documents all of its
instances, which is why 29 pages are enough for 171 modules — and why you should
look for the *methodology* page, not a page named after your exact file.

## Choosing an adder

The most common question in this area, and the one the module names answer
least well:

| If you need | Use | Why |
|---|---|---|
| Smallest area, timing is not tight | `math_adder_ripple_carry` | O(n) delay, minimal logic. Fine at 8 bits, painful at 32 |
| A balance at moderate width | `math_adder_brent_kung` | O(log n) depth with far fewer cells than Kogge-Stone |
| Fastest at wide widths, area available | `math_adder_han_carlson` | Hybrid: Kogge-Stone-like depth, Brent-Kung-like wiring |
| To sum three or more operands | `math_adder_carry_save` | Defers the carry chain; finish with one real adder |
| A partial-product tree | `math_compressor_4to2` | The cell Dadda and Wallace trees are built from |

The prefix adders share `math_prefix_cell` and `math_prefix_cell_gray`; those
two pages explain the group-generate/propagate algebra that all of them use.

## Floating point

The four formats are the same pipeline in different widths — unpack, align,
operate, normalize, round, repack — so the per-format pages
([bf16](math_bf16_adder.md), [fp16](math_fp16_modules.md),
[fp32](math_fp32_modules.md), [fp8](math_fp8_modules.md)) are best read after
one of them. Start with [bf16](math_bf16_adder.md): it has the fewest mantissa
bits, so the worked examples stay short, and the
[extended set](math_bf16_extended.md) shows what a fully-built-out format looks
like once conversions, comparisons and activations are added.

The mantissa multipliers are the integer Dadda trees from the first half of the
library. The two halves are not separate collections.

## Related

- [rtl-common](../rtl-common/overview.md) — the counters, FIFOs and encoders this
  library builds on
- [rtl-cdc](../rtl-cdc/overview.md) — if an arithmetic block spans clock domains,
  the crossing belongs there, not here
