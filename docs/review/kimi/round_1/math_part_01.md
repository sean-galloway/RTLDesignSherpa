# Review: math_part_01 (RTL Math Library, part 1 of 3)

I checked every port list, parameter, equation, worked example, and numeric claim in these 12 pages against the provided RTL, recomputing cell counts, prefix-network depths, and the arithmetic in the examples. Modules whose RTL was not in the bundle (`math_adder_half`, `math_adder_full_nbit`, `math_adder_carry_save_nbit`, `math_addsub_full_nbit`, the `math_prefix_cell*` cells, and everything in `math_bf16_extended.md`) could only be checked for internal consistency; that is noted where relevant. Timing/frequency/LUT tables were treated as known-weak estimates and skipped unless internally contradictory or recomputably wrong.

---

## Findings

```
[CONFIRMED] Carry-save page's central claim — "the carry vector does NOT need left-shifting" — is mathematically wrong, and its own worked example disproves it
  File:     docs/markdown/RTLCommon/math_adder_carry_save.md
  Says:     "Common Misconception: The carry vector does NOT need left-shifting. The CSA already accounts
             for weight alignment internally." / "WRONG: Don't shift carry vector!
             assign final_result = sum_vec + {carry_vec, 1'b0};  // INCORRECT!" / worked example:
             "assign final_result = {1'b0, sum_vec} + {1'b0, carry_vec}; ... assert(final_result == 9'd60);"
             for inputs 10, 20, 30.
  Actually: The single-bit cell (rtl/common/math_adder_carry_save.sv) is a full adder:
             ow_sum = a^b^c, ow_carry = ab|ac|bc. The carry bit has weight 2 relative to the sum bit —
             the page itself states "Key Property: Sum + 2×Carry = A + B + C". The final add must be
             S + (C<<1). Recomputing the page's own example: 10⊕20⊕30 gives sum_vec=8'h00,
             carry_vec=8'h1E (=30); the doc's wiring yields 0+30=30, which fails its own assert of 60;
             with the shift, 0+(30<<1)=60 as expected. The companion page
             docs/markdown/RTLCommon/math_adder_basic.md gets it right:
             "Final result: sum + (carry << 1) ... assign result = {1'b0, sum} + {carry, 1'b0};".
  Impact:   Every multi-operand example on this page (3-number, 4-number, 7-number Wallace tree,
             multiplier partial-product reduction) feeds carry vectors into the next stage unshifted,
             so a reader following it builds trees that compute wrong sums. This is the most damaging
             defect in the book. (The N-bit module's RTL was not in the bundle, but the page's port
             table says ow_carry is "NOT shifted" and its implementation snippet is a per-bit array of
             these cells, so the error stands on the page's own terms.)
```

```
[CONFIRMED] Library map claims the FP "exponent path uses a Han-Carlson prefix adder" — the bf16 exponent adder is plain behavioral arithmetic with no prefix-adder instance
  File:     docs/markdown/RTLCommon/math_library.md
  Says:     "the **exponent path** uses a Han-Carlson prefix adder" and table row
             "| Exponent add | `math_*_exponent_adder` | Han-Carlson prefix adder |"
  Actually: rtl/common/math_bf16_exponent_adder.sv instantiates no submodules; the exponent math is one
             behavioral expression:
             "assign w_exp_sum_raw = {2'b0, i_exp_a} + {2'b0, i_exp_b} + {9'b0, i_norm_adjust} - 10'd127;".
             The module's own detail page (math_bf16_exponent_adder.md) describes it as simple 10-bit
             arithmetic ("10-bit adder | ~15" LUTs), contradicting the map. The fp16/fp32/fp8 exponent
             adders were not in the bundle, so the claim is disproven for bf16 and unverified
             (SUSPECTED) for the other formats the table generalizes to ("per format").
  Impact:   A reader looking for the Han-Carlson exponent core inside the FP units will not find it;
             the "FP cores are built from the integer methodologies" narrative is overstated for the
             exponent path.
```

```
[CONFIRMED] addsub multi-function ALU example: the ALU_INC case returns A, not A+1
  File:     docs/markdown/RTLCommon/math_addsub.md
  Says:     "ALU_INC: begin b_mux = 8'b0; ctrl = 1'b1;      // A + 0 + 1 = A + 1 end"
  Actually: By the page's own equations (w_ip[i] = i_b[i] ^ i_c, w_c[0] = i_c), ctrl=1 forces subtract
             semantics: result = A + ~0 + 1 = A + 8'hFF + 1 ≡ A (mod 256), with carry set. The comment
             "A + 0 + 1" is unrealizable with this port list — i_c is simultaneously the invert-B
             control and the carry-in, so add mode (i_c=0) can never inject a carry. No single-pass
             input combination produces A+1. (Module RTL not in bundle; this is an internal
             contradiction proven from the page's own logic description.)
  Impact:   Anyone copying the multi_alu example gets an increment operation that does nothing.
```

```
[CONFIRMED] Half-adder parity-generator example cannot compile
  File:     docs/markdown/RTLCommon/math_adder_basic.md
  Says:     "genvar i;
             generate
                 if (i == 0) begin
                     assign parity_chain[0] = data[0];
                 end else begin
                     math_adder_half u_parity ( .i_a(data[i]), .i_b(parity_chain[i-1]), ... );"
  Actually: The genvar i is never driven by a generate-for loop, so `if (i == 0)` is not a constant
             expression, and `parity_chain` is never declared. The intended XOR chain needs a
             `for (i = 0; i < 8; i++)` around the if/else and a `logic [7:0] parity_chain;` declaration.
  Impact:   Copy-paste example fails at elaboration.
```

```
[CONFIRMED] Han-Carlson page says only 16-bit and 48-bit variants exist; the RTL provides six widths and the library map lists all six
  File:     docs/markdown/RTLCommon/math_adder_han_carlson.md
  Says:     "**Available widths:** 16-bit, 48-bit (auto-generated for BF16 arithmetic)" and lists only
             math_adder_han_carlson_016.sv and math_adder_han_carlson_048.sv as top-level modules.
  Actually: The RTL bundle contains math_adder_han_carlson_{016,022,032,044,048,072}.sv, all from the
             same generator. docs/markdown/RTLCommon/math_library.md correctly lists
             "math_adder_han_carlson_{016,022,032,044,048,072}".
  Impact:   The 22/32/44/72-bit variants (used by other FP formats) are undiscoverable from this page,
             and two pages of the same book disagree.
```

```
[CONFIRMED] Brent-Kung 64-bit variant exists in RTL but is omitted from both width lists
  File:     docs/markdown/RTLCommon/math_adder_brent_kung.md
  Says:     "Available widths: **8-bit**, **16-bit**, **32-bit**" (math_library.md likewise:
             "math_adder_brent_kung_{008,016,032}").
  Actually: rtl/common/math_adder_brent_kung_064.sv (N=64) and
             rtl/common/math_adder_brent_kung_grouppg_064.sv are present in the bundle.
  Impact:   The 64-bit adder is invisible to readers; the width and area/timing tables are incomplete.
```

```
[CONFIRMED] bf16 adder latency overstated by one cycle in the formula, the table, and the examples
  File:     docs/markdown/RTLCommon/math_bf16_adder.md
  Says:     "**Latency Formula:** `1 + PIPE_STAGE_1 + PIPE_STAGE_2 + PIPE_STAGE_3 + PIPE_STAGE_4` cycles";
             "| [1,1,1,1] | 5 cycles | Maximum frequency |";
             "// With [1,1,1,1] config, wait 5 cycles for result".
  Actually: The RTL contains exactly four optional register stages (gen_pipe1 … gen_pipe4) and is
             combinational otherwise; ow_valid = r4_valid. With all four enabled, the output is valid
             4 clock edges after the input is sampled; with all disabled the path is 0-cycle
             combinational. Every configuration is overstated by one. The "+1" has no corresponding
             register. (The RTL header comment repeats the same formula — see POSSIBLE RTL BUGS.)
  Impact:   Latency budgets and testbench waits are off by one cycle (conservative direction, but wrong).
```

```
[CONFIRMED] Brent-Kung page gives three different 32-bit logic-depth totals (11, 12, 13) and two different reverse-tree depths
  File:     docs/markdown/RTLCommon/math_adder_brent_kung.md
  Says:     "**Total depth**: 2×log2(N) + 1 levels" (=11 for N=32);
             "**Logic Level Breakdown (32-bit):** ... 5. **Total**: 12 levels";
             delay table "| 32-bit | 13 | ~3.0 | ~333 MHz |";
             also "Reverse tree depth: log2(N) - 1 levels" (=4) vs. breakdown "Reverse tree: 5 levels".
  Actually: The three totals are mutually inconsistent. From the generated network
             (rtl/common/math_adder_brent_kung_grouppg_032.sv) the longest prefix chain is 8 cell levels
             (gray_1_0 → gray_3_0 → gray_7_0 → gray_15_0 → gray_23_15 → gray_27_23 → gray_29_27 →
             gray_30_29), i.e., 10 cell levels including bitwise-PG and sum stages.
  Impact:   Minor — the depth figures cannot be used for reasoning or cross-architecture comparison.
```

```
[CONFIRMED] CSA-tree "number of stages" formula contradicts all three of its own examples
  File:     docs/markdown/RTLCommon/math_adder_carry_save.md
  Says:     "N operands → ceil(log_1.5(N)) CSA stages + 1 final adder
             Example: 3 operands: 1 CSA + 1 adder / 7 operands: 4 CSA + 1 adder / 15 operands: 6 CSA + 1 adder"
  Actually: ceil(log_1.5(3)) = 3, ceil(log_1.5(7)) = 5, ceil(log_1.5(15)) = 7 — the formula matches none
             of the examples. The example stage counts are correct Wallace-tree depths (recurrence
             D(n) = 1 + D(⌈2n/3⌉): D(3)=1, D(7)=4, D(15)=6); it is the closed-form formula that is wrong.
  Impact:   Minor; readers applying the formula over-provision tree depth.
```

```
[CONFIRMED] Brent-Kung 32-bit area breakdown claims "~50" black cells; the generated netlist has 26 black and 32 gray
  File:     docs/markdown/RTLCommon/math_adder_brent_kung.md
  Says:     "Black cells (forward): ~50 cells × 3 gates = 150 LUTs
             Gray cells (reverse): ~30 cells × 2 gates = 60 LUTs ... **Total**: ~306 LUTs"
  Actually: Counting instantiations in rtl/common/math_adder_brent_kung_grouppg_032.sv: 26 black cells
             (15+7+3+1 across the four forward levels) and 32 gray cells (16 intermediate + 16 fill).
             Under the doc's own gate model: 64 (PG) + 26×3 + 32×2 + 32 (sum) ≈ 238 LUTs, not ~306.
  Impact:   Black-cell count ~2× overstated; total area estimate ~30% high.
```

```
[CONFIRMED] Han-Carlson cell-count tables do not match the generated netlists
  File:     docs/markdown/RTLCommon/math_adder_han_carlson.md
  Says:     "| 16-bit | ~31 | 8 | ~39 | ~80 |" and "| 48-bit | ~96 | 24 | ~120 | ~250 |"
             (Black / Gray / Total / LUTs); also "Prefix Cells (16-bit) ... Han-Carlson ~39".
  Actually: The generate loops in rtl/common/math_adder_han_carlson_016.sv instantiate math_prefix_cell
             7+7+6+4 = 24 times and math_prefix_cell_gray 8 times → 32 cells total (not ~31 black/~39
             total). rtl/common/math_adder_han_carlson_048.sv: 23+23+22+20+16+8 = 112 black + 24 gray
             = 136 cells (not ~96/~120).
  Impact:   The area numbers anchoring the "Why Han-Carlson is Optimal" comparison (including
             "~40% fewer cells than Kogge-Stone") are off by ~15–30%.
```

```
[CONFIRMED] Regeneration instructions contradict the RTL headers (and each other) about which generator owns which files
  File:     docs/markdown/RTLCommon/math_adder_han_carlson.md
  Says:     "**Generator:** `bin/rtl_generators/bf16/han_carlson_adder.py`
             **Regenerate:** `PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/generate_all.py rtl/common`"
  Actually: Every Han-Carlson RTL header says "Generator: bin/rtl_generators/ieee754/han_carlson_adder.py /
             Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py".
             Conversely, docs/markdown/RTLCommon/math_bf16_extended.md says "Regenerate all BF16 modules:
             ... bin/rtl_generators/ieee754/generate_all.py", but rtl/common/math_bf16_exponent_adder.sv's
             header names bin/rtl_generators/bf16/bf16_exponent_adder.py and bf16/generate_all.py.
  Impact:   Given the repo's own rule (stated in math_library.md) that a generator change requires
             regenerating everything that generator owns, pointing readers at the wrong generator is a
             real hazard: they will either fail to find the script or regenerate an incomplete set.
```

```
[CONFIRMED] pg_chain page: "1 bit (degenerates to half adder)" — it degenerates to a full adder
  File:     docs/markdown/RTLCommon/math_adder_pg_chain.md
  Says:     "**Minimum**: 1 bit (degenerates to half adder)"
  Actually: The carry input is used at every width — "assign w_c[0] = i_c;" and
             "ow_sum[i] = w_p[i] ^ w_c[i];" — so at N=1 the circuit computes sum = a⊕b⊕cin,
             carry = ab | cin·(a⊕b): a full adder. (math_adder_ripple_carry.md states this correctly:
             "degenerates to single full adder".)
  Impact:   Trivial factual slip.
```

```
[CONFIRMED] Cross-reference to non-existent module "math_adder_brent_kung_nbit"
  File:     docs/markdown/RTLCommon/math_adder_han_carlson.md
  Says:     "- **math_adder_brent_kung_nbit** - Alternative area-optimized adder"
  Actually: No `_nbit` Brent-Kung module exists in the RTL bundle or in the library map; the family is
             explicitly fixed-width (math_adder_brent_kung_{008,016,032,064}) because, as
             math_adder_brent_kung.md itself states, "The parallel prefix network structure is
             width-specific".
  Impact:   Broken cross-reference.
```

---

## POSSIBLE RTL BUGS

1. **`rtl/common/math_bf16_adder.sv` header comment (comment bug).** The header states "Latency: 1 + PIPE_STAGE_1 + PIPE_STAGE_2 + PIPE_STAGE_3 + PIPE_STAGE_4 cycles", but the module implements at most four register stages (r1→r4), so the structural maximum is 4 cycles, not 5. This comment is the apparent source of the doc's off-by-one (Finding 7 above).

2. **`rtl/common/math_bf16_adder.sv` — overflow/underflow flags are not mutually exclusive (latent, currently benign).** `wire w_exp_underflow = w_exp_adjusted[8] || (w_exp_adjusted[7:0] == 8'h00);` — `w_exp_adjusted[8]` is also set when exp_l = 8'hFF increments to 9'h100 (add-overflow path), asserting overflow and underflow simultaneously. It is harmless today because that situation only arises for inf/NaN inputs, which the result mux handles in earlier branches, and overflow is checked before underflow. Worth a one-line comment or a `~w_exp_overflow &` qualifier to make the intent explicit.

No functional RTL bugs found in the provided files. I traced the bf16 adder's alignment, sticky-mask, normalization (including the add-overflow right-shift GRS bookkeeping), and RNE rounding bit extraction — all consistent.

---

## Overall assessment

Interface-level accuracy is high: every module present in the bundle has its ports, parameters, and core equations documented correctly (full adder, carry-save cell, pg_chain, ripple, both bf16 modules, the Han-Carlson and Brent-Kung top levels), and the `math_adder_pg_chain.md` naming caveat and the Han-Carlson depth-formula clarification are examples of the documentation being commendably honest about its own weaknesses. The serious defects are concentrated: (1) the carry-save page's "do not shift the carry" claim, which is flatly wrong, contradicts the companion basic-adder page, fails its own worked example, and poisons every multi-operand example on the page; (2) module-inventory gaps — the Han-Carlson page hides four of the six generated widths and both pages hide the 64-bit Brent-Kung, so the book undersells what the RTL actually provides; (3) the library map's unsupported "Han-Carlson exponent adder" claim; and (4) recomputable numbers (latency, prefix-cell counts, tree-depth formulas) that disagree with the netlists or with each other. The bf16 adder/multiplier support pages are otherwise careful and match the RTL closely. Everything in `math_bf16_extended.md` and the pages for `math_adder_half`, `math_adder_full_nbit`, `math_adder_carry_save_nbit`, and `math_addsub_full_nbit` could not be verified against RTL in this bundle and should be re-checked in parts 2/3 if their RTL appears there.