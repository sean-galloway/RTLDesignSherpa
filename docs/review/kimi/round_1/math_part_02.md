# Review: math_part_02 (RTL Math Library, part 2 of 3)

Scope verified: all 12 doc pages read in full. For the 13 modules whose RTL was provided (bf16_fma, bf16_mantissa_mult, bf16_multiplier, compressor_4to2, dadda_4to2_008/011/024, dadda_tree_008/016/032, wallace_tree_008/016/032) I checked declarations, code excerpts, special-case logic, and recomputed all structural counts. For `math_fp16/fp32/fp8/ieee754/multiplier_basic` pages, no module RTL was in the bundle — those pages were checked for internal consistency and arithmetic only.

Verification notes on counts: Dadda 8x8 = 35 CSA + 7 HA (verified exactly, matches textbook and bit conservation); Wallace 8x8 = 36 FA + 25 HA and Wallace 16x16 = 196 FA + 78 HA (both verified exactly by recounting instances in the RTL); dadda_4to2_008 = 39 compressors + 2 FA + 0 HA (verified exactly).

---

## Findings

```
[CONFIRMED] bf16_fma special-case priority section omits three RTL branches and misrepresents the zero-addend branch
  File:     docs/markdown/RTLCommon/math_bf16_fma.md
  Says:     "end else if (w_c_eff_zero) begin
                 // 5. Zero addend: product only
                 ow_result = {w_prod_sign, w_prod_exp[7:0], w_prod_mant_ext[22:0]};"
  Actually: The RTL's w_c_eff_zero branch first checks product overflow/underflow:
                "if (w_prod_exp > 10'd254) begin
                     ow_result = {w_prod_sign, 8'hFF, 23'h0};  // Overflow to inf
                     ow_overflow = 1'b1;
                 end else if (w_prod_underflow) ... ow_underflow = 1'b1;"
            The doc also omits two entire branches present in the RTL:
            "w_prod_is_zero & w_c_eff_zero" -> {w_prod_sign & w_sign_c, 8'h00, 23'h0}
            (IEEE signed-zero for 0*x + 0), and "w_sum_abs == 48'h0" -> 32'h0
            (exact-cancellation +0).
  Impact:   For A*B + 0 where A*B overflows (e.g. 2^100 * 2^100 + 0), the doc says the
            output is the raw product bits with no flag; the RTL outputs +Inf with
            ow_overflow=1. For (+1.0 * 0) + (-0), the doc's chain yields -0; the RTL
            (and IEEE 754 RNE) yields +0. A reader implementing or verifying against
            this section gets the edge-case behavior wrong.
```

```
[CONFIRMED] bf16_multiplier special-case priority order contradicts the RTL (doc: NaN > Inf > Zero; RTL: NaN > Zero > Inf)
  File:     docs/markdown/RTLCommon/math_bf16_multiplier.md
  Says:     "if (w_any_nan | w_invalid_op) ...
             end else if (w_result_inf | w_final_overflow) begin
                 // 2. Infinity: inf input or overflow
             end else if (w_result_zero | w_exp_underflow) begin
                 // 3. Zero: zero input or underflow"
  Actually: RTL order is NaN, then Zero, then Inf/Overflow, then Underflow, with the
            explicit comment: "Zero MUST be checked before overflow because when either
            input is zero, the exponent adder produces a garbage value (e.g. 0xFF) that
            falsely triggers the overflow path." Zero and underflow are separate
            branches; the doc merges them.
  Impact:   The documented algorithm is genuinely wrong, not just reordered: with
            a = 0 (or subnormal) and b with exp_b = 126, the exponent adder yields
            exp_sum_raw = -1, whose low 8 bits are 0xFF, setting w_final_overflow while
            w_result_zero is also true. The doc's chain would output infinity with
            ow_overflow=1; the RTL correctly outputs signed zero. Anyone reimplementing
            from the doc reproduces the bug the RTL comment warns about.
```

```
[CONFIRMED] bf16_multiplier claims NaN output has sign=0; RTL preserves the computed result sign
  File:     docs/markdown/RTLCommon/math_bf16_multiplier.md
  Says:     "Canonical qNaN - 0x7FC0 (sign=0, exp=FF, mant=0x40)" (Design Considerations
            -> NaN Handling; also "Input NaN - Propagated to output as canonical quiet NaN")
  Actually: RTL emits "ow_result = {w_sign_result, 8'hFF, 7'h40};" with the comment
            "quiet NaN with sign preserved". For e.g. -2.0 * NaN the output is 0xFFC0,
            not 0x7FC0. The doc's own code excerpt on the same page shows
            {w_sign_result, 8'hFF, 7'h40}, so the page also contradicts itself.
  Impact:   Readers checking NaN encodings against the doc will see an unexpected sign
            bit on half of all NaN-producing inputs.
```

```
[CONFIRMED] FP8 page gives E5M2 minimum range ~250x too small
  File:     docs/markdown/RTLCommon/math_fp8_modules.md
  Says:     "FP8 E5M2 Format: Range: ~6e-8 to 57344 (has infinity)"
  Actually: E5M2 minimum subnormal is mant=01, exp=0 = 0.25 * 2^(1-15) = 2^-16 ~ 1.5e-5;
            minimum normal is 2^-14 ~ 6.1e-5. The page's own format-comparison table
            correctly states "Min normal: 6.1e-5" for E5M2, so the page contradicts
            itself. ~6e-8 is FP16's minimum subnormal (2^-24), apparently copied from
            the FP16 page. Recomputed: 2^-16 = 1.526e-5.
  Impact:   Wrong dynamic-range bound for the E5M2 format; internal contradiction.
```

```
[CONFIRMED] dadda_4to2 page claims "~25% fewer reduction stages" and gives component counts off by up to 3x
  File:     docs/markdown/RTLCommon/math_multiplier_dadda_4to2.md
  Says:     (a) Overview: "providing fast parallel multiplication with ~25% fewer
                reduction stages than traditional 3:2 CSA-based Dadda trees"
            (b) Resource table: "4:2 Compressors ~12-15", "Full Adders (3:2) ~8-12",
                "Half Adders ~4-6"
            (c) Component Instantiation excerpt includes
                "math_adder_half u_ha_01_000 (.i_a(w_pp_0_1), .i_b(w_pp_1_0), ...)"
  Actually: (a) math_multiplier_dadda_4to2_008 has 4 reduction stages (RTL comments:
                "height 8 -> 6", "6 -> 4", "4 -> 3", "3 -> 2"); the repo's own 3:2
                math_multiplier_dadda_tree_008 also has 4 stages ("max column height
                6, 4, 3, 2"). The stage counts are identical, not 25% fewer.
            (b) Counted exactly in the RTL: 39 math_compressor_4to2 instances
                (8+16+11+4 by stage), 2 math_adder_full (u_fa_02_000, u_fa_10_001),
                and ZERO math_adder_half instances.
            (c) No u_ha_01_000 exists anywhere in the module; column 1 passes
                w_pp_0_1 / w_pp_1_0 straight into the CPA operand rows.
  Impact:   The headline architectural advantage is unsupported for the module the page
            documents, and the resource table misleads area estimates by 2.5-3x
            (39 vs "~12-15" compressors). The instantiation excerpt shows a module
            instance that does not exist in the RTL.
```

```
[SUSPECTED] ieee754 page claims an "inexact" status flag that no shown interface or table supports
  File:     docs/markdown/RTLCommon/math_ieee754_modules.md
  Says:     Key Features: "Status flags - Overflow, underflow, invalid, inexact"
  Actually: Every interface on the page (math_ieee754_2008_fp16_adder, fp32_multiplier,
            fp32_fma) and the Status Flags table list only ow_overflow, ow_underflow,
            ow_invalid. No ow_inexact port appears anywhere. The RTL for these modules
            was not in the review bundle, so I could not confirm whether inexact exists.
  Impact:   Reader may write testbenches expecting an inexact flag that is not there.
```

---

## POSSIBLE RTL BUGS / RTL NOTES

1. **Stale header comment (comment-only)** — `rtl/common/math_multiplier_dadda_4to2_011.sv` says "Dadda 11x11 multiplier with 4:2 compressors for FP32 mantissa". 11x11 is the FP16 mantissa size (10 explicit + 1 implied bit); FP32 uses the 24x24 variant. The doc page (`math_ieee754_modules.md`) correctly assigns this module to FP16.

2. **Stale comment (comment-only)** — `rtl/common/math_bf16_fma.sv` above the CLZ instantiation: "To get actual leading zeros from MSB, we bit-reverse the input / Bit-reverse function for 48-bit value". No bit reversal is performed, and none is needed — `count_leading_zeros` now scans MSB-down (its own header documents the fix). The comment is a leftover from the pre-fix revision.

3. **Design caveat (not necessarily a bug)** — `math_bf16_fma` drops all bits shifted out during alignment (`w_mant_smaller_shifted = ... >> w_shift_clamped`), so sticky information below the 48-bit window is lost; rounding is not exact IEEE RNE for large exponent differences. Acceptable for the simplified AI-training family (which explicitly uses FTZ and does not claim full compliance), but it is not documented anywhere.

## Gaps noted (not findings)

- `math_fp16_modules.md`, `math_fp32_modules.md`, `math_fp8_modules.md`, `math_ieee754_modules.md`, `math_multiplier_basic.md`: none of the modules cataloged by these pages had RTL in the bundle, so only internal consistency and arithmetic could be checked.
- The Wallace page documents `math_multiplier_wallace_tree_csa_008/016/032` variants; those files were not in the RTL bundle, so the "two variants, structurally identical" claim is unverified. The plain variants were verified.

## Overall accuracy

Mixed, and polarized by page. The two multiplier-tree pages (`math_multiplier_dadda_tree.md`, `math_multiplier_wallace_tree.md`) are excellent — every structural claim I could check (stage counts 4/6/8, Dadda 35+7=42 cells at 8x8, Wallace 36+25=61 at 8x8 and 196+78=274 at 16x16, Brent-Kung CPA widths, CPA row contents) matched the RTL exactly after a full instance recount. `math_bf16_mantissa_mult.md` and `math_compressor_4to2.md` are also accurate, including the guard/round/sticky bit mapping. Against that, both BF16 top-level pages document a special-case priority chain that is materially different from the RTL — and in the multiplier's case, the documented order would produce infinity where the RTL correctly produces zero. The `math_multiplier_dadda_4to2.md` page has the worst numeric problems: component counts off by up to 3x, a half-adder instance in an excerpt that does not exist, and a headline "25% fewer stages" claim contradicted by the repo's own 3:2 Dadda module. The FP8 page has one clear numeric error (E5M2 range). The special-case sections of the two BF16 pages should be rewritten to match the RTL branch structure verbatim.