# Review: math_part_02 — RTL Math Library (12 docs)

I verified every checkable claim against the provided RTL. The 12 pages split into three groups: (a) core-module pages with full RTL present (`math_bf16_fma`, `math_bf16_mantissa_mult`, `math_bf16_multiplier`, `math_compressor_4to2`, `math_multiplier_dadda_4to2`, `math_multiplier_dadda_tree`, `math_multiplier_basic`); (b) five catalog/overview pages (`math_bf16_extended`, `math_fp16_modules`, `math_fp32_modules`, `math_fp8_modules`, `math_ieee754_modules`) naming ~117 modules, none of which appear in the RTL bundle; (c) `math_multiplier_carry_save`, documented in detail on the basic-multiplier page but absent from the bundle.

---

## Findings

```
[CONFIRMED] Special-case priority order in bf16 multiplier doc contradicts RTL; doc order yields +inf for 0 × 0.5
  File:     docs/markdown/RTLCommon/math_bf16_multiplier.md
  Says:     "end else if (w_result_inf | w_final_overflow) begin  // 2. Infinity: inf input or overflow
             end else if (w_result_zero | w_exp_underflow) begin  // 3. Zero: zero input or underflow"
  Actually: rtl/math/math_bf16_multiplier.sv puts the zero case BEFORE the inf/overflow case:
            "end else if (w_result_zero) begin ... end else if (w_result_inf | w_final_overflow)"
            with the comment: "Zero MUST be checked before overflow because when either input
            is zero, the exponent adder produces a garbage value (e.g. 0xFF) that falsely
            triggers the overflow path."
            Recomputation of the failing case (a = 16'h0000 (+0), b = 16'h3F00 (0.5, exp=126)):
            in math_bf16_exponent_adder, w_exp_sum_raw = 0 + 126 + 0 - 127 = -1, so
            ow_exp_out = raw[7:0] = 8'hFF (ow_underflow is masked by w_either_special).
            Back in the multiplier, w_final_overflow = (w_exp_final == 8'hFF) = 1.
            Doc's order -> branch 2 fires -> result = +inf, ow_overflow = 1.
            RTL's order  -> zero branch fires -> result = +0. (RTL is correct.)
  Impact:   A reader implementing the documented priority produces +inf with the overflow
            flag for 0 × (any operand with exponent <= 126) instead of a signed zero.
```

```
[CONFIRMED] "RNE rounding" claimed for the BF16 multiplier, but the logic does not implement Round-to-Nearest-Even
  File:     docs/markdown/RTLCommon/math_bf16_multiplier.md (also math_bf16_mantissa_mult.md)
  Says:     "RNE rounding - Round-to-Nearest-Even for unbiased results" and, in
            math_bf16_mantissa_mult.md: "Round up if: Guard AND (Round OR Sticky OR LSB)"
  Actually: rtl/math/math_bf16_mantissa_mult.sv folds the guard bit into the sticky output:
            ow_sticky_bit = w_guard_norm | w_sticky_norm, and outputs the *round* bit as
            ow_round_bit. The multiplier (math_bf16_multiplier.sv) then computes
            w_round_up = w_round_bit & (w_sticky_bit | w_lsb), i.e.  R & (G | S | LSB),
            whereas RNE requires  G & (R | S | LSB).
            Divergences (G,R,S,LSB):
              (0,1,0,1): RTL rounds up at 0.25 ulp        -> RNE says no round.  WRONG.
              (0,1,1,x): RTL rounds up at 0.375 ulp       -> RNE says no round.  WRONG.
              (1,0,0,1): RTL truncates an exact tie to odd -> RNE rounds to even. WRONG.
              (1,0,1,x): RTL truncates a >0.5-ulp value    -> RNE rounds up.      WRONG.
            4 of 8 guard/round/sticky patterns diverge. The BF16 FMA implements RNE
            correctly (w_round_up = w_guard & (w_round | w_sticky | w_mant_23[0])); only
            the mantissa_mult/multiplier path is affected. See POSSIBLE RTL BUGS.
  Impact:   BF16 multiply results can be off by 1 ulp in both directions; the advertised
            unbiased RNE behavior is not delivered.
```

```
[SUSPECTED] Five catalog pages document ~117 modules; the RTL bundle contains none of them
  File:     docs/markdown/RTLCommon/math_bf16_extended.md, math_fp16_modules.md,
            math_fp32_modules.md, math_fp8_modules.md, math_ieee754_modules.md
  Says:     e.g. "math_bf16_goldschmidt_div #(parameter int ITERATIONS = 2,
            parameter int PIPELINED = 1, parameter int LUT_DEPTH = 128)" with a
            clk/rst/valid interface; "math_bf16_fast_reciprocal #(parameter int
            LUT_DEPTH = 128)"; pipelined "math_ieee754_2008_fp16_adder #(PIPE_STAGE_1..4)".
  Actually: The RTL banner states "11 documented modules + 18 dependencies", and the 11 are
            accounted for entirely by the core pages (bf16_fma, bf16_mantissa_mult,
            bf16_multiplier, compressor_4to2, multiplier_basic_cell, dadda_4to2_008/011/024,
            dadda_tree_008/016/032). By my count the five pages name 117 distinct modules
            (29 + 17 + 17 + 44 + 10); excluding the few core BF16 modules that do exist,
            ~113 named modules appear nowhere in the ground truth. The whole math book is
            billed as 31 modules across all three parts, so most of these cannot exist.
            Existence elsewhere cannot be disproved from this unit, hence SUSPECTED.
  Impact:   Readers may instantiate modules that were never written; every interface,
            parameter, latency, and special-value claim on these pages is unverifiable.
```

```
[SUSPECTED] math_multiplier_carry_save documented in full detail but has no RTL in the bundle
  File:     docs/markdown/RTLCommon/math_multiplier_basic.md
  Says:     "module math_multiplier_carry_save #(parameter int N = 4) (input logic [N-1:0]
            i_multiplier, i_multiplicand, output logic [2*N-1:0] ow_product);" plus a
            generate-loop "Implementation" code block, the 5×6=30 worked example, and
            per-width timing/resource tables.
  Actually: No math_multiplier_carry_save module exists in the provided RTL. The only
            similarly-named module, rtl/math/math_adder_carry_save.sv, is a single-bit
            3:2 compressor — a different module. The page's other module,
            math_multiplier_basic_cell, is present and matches its documentation exactly.
  Impact:   Roughly two-thirds of the page (declaration, parameters, ports, array
            structure, usage examples, timing and LUT tables) describes a module that
            cannot be verified and may not exist.
```

```
[CONFIRMED] Dadda 4:2 page: component counts, stage-savings claim, and worked examples are wrong
  File:     docs/markdown/RTLCommon/math_multiplier_dadda_4to2.md
  Says:     Resource table: "4:2 Compressors ~12-15; Full Adders (3:2) ~8-12; Half Adders
            ~4-6"; header: "~25% fewer reduction stages than traditional 3:2 CSA-based
            Dadda trees"; comparison table: "Total adders/compressors ~50 (3:2) vs ~35 (4:2)";
            example instances "math_compressor_4to2 u_c4to2_07_000" and
            "math_adder_half u_ha_01_000"; Column-7 example: one 4:2 compressor reduces
            height 8 -> "Height after: 6".
  Actually: Counted from rtl/math/math_multiplier_dadda_4to2_008.sv: 39 math_compressor_4to2
            instances (8 + 16 + 11 + 4 across the four stages), 2 math_adder_full
            (u_fa_02_000, u_fa_10_001), and 0 math_adder_half — the u_ha_01_000 example
            instance does not exist, nor do any half adders; the first column-7 compressor
            is named u_c4to2_07_001, not u_c4to2_07_000. Both this multiplier (stage
            comments "8->6, 6->4, 4->3, 3->2") and math_multiplier_dadda_tree_008
            ("6, 4, 3, 2") have exactly 4 reduction stages, so the "~25% fewer stages"
            headline is false. Column 7 in stage 1 uses TWO compressors (u_c4to2_07_001
            and u_c4to2_07_002), and the doc's own worked example lists sum1 + pp43..pp70
            + 2 carries = 7 bits while claiming "Height after: 6".
  Impact:   Area/complexity figures are off by ~3x for compressors; the comparative
            advantage over the 3:2 Dadda tree is misstated.
```

```
[CONFIRMED] BF16 FMA special-case pseudocode omits RTL branches; doc yields -0 and missing overflow/underflow flags in corner cases
  File:     docs/markdown/RTLCommon/math_bf16_fma.md
  Says:     "Special Case Priority" block lists 7 cases: "... 4. Zero product: pass-through
            addend — ow_result = i_c;  5. Zero addend: product only —
            ow_result = {w_prod_sign, w_prod_exp[7:0], w_prod_mant_ext[22:0]}; ..."
  Actually: rtl/math/math_bf16_fma.sv has two additional branches —
            (w_prod_is_zero & w_c_eff_zero) -> {w_prod_sign & w_sign_c, 8'h00, 23'h0}, and
            (w_sum_abs == 48'h0) -> 32'h0 — and the zero-addend branch itself contains
            product overflow (w_prod_exp > 254 -> inf + ow_overflow) and product underflow
            (-> zero + ow_underflow) sub-checks.
            Concrete 1: a=+0, b=2.0, c=-0 (0x80000000): doc branch 4 passes through i_c =
            -0; RTL's both-zero branch yields +0, which is the IEEE-754 RNE-correct answer.
            Concrete 2: a = max-normal BF16, b = 4.0, c = +0: doc branch 5 emits
            {sign, exp[7:0], mant} with no overflow check (a small normal number with the
            wrapped exponent); RTL emits +inf with ow_overflow = 1.
  Impact:   Wrong sign of zero and silently dropped overflow/underflow flags for anyone
            implementing from the documented algorithm.
```

```
[CONFIRMED] NaN prose says sign=0; RTL (and the page's own code block) preserve the result sign
  File:     docs/markdown/RTLCommon/math_bf16_multiplier.md
  Says:     "Canonical qNaN - 0x7FC0 (sign=0, exp=FF, mant=0x40)"
  Actually: rtl/math/math_bf16_multiplier.sv: "ow_result = {w_sign_result, 8'hFF, 7'h40};"
            — the NaN sign is the XOR of the input signs, not forced to 0. The page's own
            "Special Case Priority" code block shows the same {w_sign_result, ...}
            expression, contradicting its prose.
  Impact:   Minor; a reader checking the NaN output sign against the documented constant
            0x7FC0 will see 0xFFC0-class results when the product sign is negative.
```

```
[CONFIRMED] E5M2 "Range: ~6e-8" is unattainable in the format
  File:     docs/markdown/RTLCommon/math_fp8_modules.md
  Says:     "FP8 E5M2 Format: [7]=Sign, [6:2]=Exponent (5 bits, bias=15), [1:0]=Mantissa
            ... Range: ~6e-8 to 57344 (has infinity)"
  Actually: Recompute from the format definition: min normal E5M2 = 2^(1-15) = 2^-14
            ~ 6.1e-5 (which the page's own comparison table correctly states), and the
            smallest positive subnormal = 2^-14 * 2^-2 = 2^-16 ~ 1.5e-5. 6e-8 ~ 2^-24 is
            the FP16 subnormal minimum (the FP16 page's "~6.0e-8" is correct for FP16) and
            is not representable in E5M2 by a factor of ~250x.
  Impact:   Minor numeric error in the format box; overstates E5M2's small-magnitude reach.
```

---

## POSSIBLE RTL BUGS

1. **`math_bf16_mantissa_mult` produces non-RNE rounding bits (affects `math_bf16_multiplier`).**
   `ow_sticky_bit` incorrectly includes the guard bit (`w_guard_norm | w_sticky_norm`), while `ow_round_bit` carries the round bit. The consumer computes `round_up = R & (G | S | LSB)` instead of RNE's `G & (R | S | LSB)`. As shown in the findings above, 4 of 8 (G,R,S) patterns round incorrectly in both directions. The likely intended fix is to output the guard bit separately (or have the consumer compute `G & (R | S | LSB)`). Note `math_bf16_fma` does its own rounding correctly, so the bug is confined to the mantissa-mult/multiplier path. High confidence — pure combinational analysis.

2. **Stale/misleading comment in `rtl/math/math_bf16_fma.sv` (comment-level, not functional).**
   Above `u_clz`: "To get actual leading zeros from MSB, we bit-reverse the input" — but `w_sum_abs` is connected directly, and `count_leading_zeros` already scans MSB-down (its own header warns: "do not reintroduce a reversal at the call site"). The documentation page correctly describes the direct connection; the RTL comment is a leftover from the old calling convention.

---

## Overall assessment

The core-module pages are in much better shape than most documentation of this kind: module declarations, port lists, internal signal names, and even generated instance names (`HA__06_01`, `CSA_07_01`, the `w_cpa_row0/row1` packing) match the RTL line for line, and the `math_multiplier_dadda_tree.md` cell counts are exact — I independently counted 35 CSA + 7 HA in the 8-bit file and 195 CSA + 15 HA in the 16-bit file, and the 32-bit figures (899/31) satisfy the textbook Dadda formulas n²-4n+3 and n-1. The confirmed defects are concentrated and specific: the bf16_multiplier page's special-case priority order (functionally wrong for 0 × normal-exponent inputs), the "RNE" label on a rounding circuit that is not RNE (with a real RTL bug underneath), the dadda_4to2 page's component table and stage-savings claim, the FMA page's abbreviated special-case pseudocode, and the E5M2 range figure. The largest open risk is structural: the five catalog pages name roughly 113 modules with no RTL presence in this unit, and `math_multiplier_carry_save` is fully documented but absent — these pages should be verified against the repository before release, since every interface claim on them is currently unverifiable.