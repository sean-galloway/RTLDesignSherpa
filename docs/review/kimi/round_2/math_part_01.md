# Review: math_part_01 (RTL Math Library, part 1 of 3)

**Method.** I checked every module declaration, parameter, port list, and logic equation in the 11 pages against the provided RTL, and recomputed every structural number I could: Brent-Kung black/gray cell counts and prefix depths for all four widths (counted cell instances and levels in `math_adder_brent_kung_grouppg_{008,016,032,064}.sv`), and Han-Carlson black/gray counts and stage counts for all six widths (elaborated the generate conditions in each `math_adder_han_carlson_*.sv`). All of those measured tables are **exactly correct** (e.g., HC 48-bit: 112 black + 24 gray = 136, 7 prefix stages; BK 32-bit: 26 black + 32 gray, 8 prefix levels — both match my counts). The findings below are what remains after that verification.

---

## Findings

### 1. The carry-save doc teaches the wrong final summation — carry vector must be left-shifted

```
[CONFIRMED] math_adder_carry_save.md says the CSA carry output must NOT be shifted; the correct reduction is sum + (carry << 1)
  File:     docs/markdown/RTLCommon/math_adder_carry_save.md
  Says:     "// IMPORTANT: Carry vector is NOT shifted!"
            "**Common Misconception:** The carry vector does NOT need left-shifting. The CSA already
             accounts for weight alignment internally."
            "assign final_result = {1'b0, sum_vec} + {1'b0, carry_vec};"
            and under "Common Pitfalls": "// WRONG: Don't shift carry vector!
             assign final_result = sum_vec + {carry_vec, 1'b0};  // INCORRECT!"
  Actually: The carry from bit position i has weight 2^(i+1). The doc's own "Key Property" two
            paragraphs earlier states "Sum + 2×Carry = A + B + C" — the ×2 *is* the left shift.
            Recomputing the doc's own worked example (10 + 20 + 30):
              sum_vec   = 10 ^ 20 ^ 30      = 8'h00
              carry_vec = majority per bit  = 8'h1E (30)
              Doc formula:   0 + 30        = 30   -> its own "assert(final_result == 9'd60)" FAILS
              Correct:       0 + (30 << 1) = 60
            The doc also contradicts math_adder_basic.md ("Full Adder: Carry-Save Adder Stage"),
            which correctly uses "result = {1'b0, sum} + {carry, 1'b0}", and math_adder_full.md's
            CSA example, which connects ".ow_carry(carry_vector[i+1])" — again the shift.
            Everything downstream is infected: the "Adding 4 Numbers" tree feeds carry1 into the
            second CSA unshifted, and the 3-number, 4-number and 7-number final adds are all
            sum+carry. "Anti-Pattern 1" brands the only correct code on the page as wrong.
  Impact:   This is the most damaging defect in the book. A reader building an adder tree or
            multiplier reduction from this page gets silently wrong arithmetic, and the page
            actively discourages the fix.
```

### 2. Library overview claims every format's exponent adder is a Han-Carlson prefix adder — the bf16 one is behavioral

```
[CONFIRMED] math_library.md overgeneralizes the integer-core reuse claim
  File:     docs/markdown/RTLCommon/math_library.md
  Says:     "Each format's core operators are assembled from the integer methodologies above:
             the **exponent path** uses a Han-Carlson prefix adder and the **mantissa multiply**
             uses a Dadda 4:2 tree."
            and in the Core operators table: "| Exponent add | `math_*_exponent_adder` |
             Han-Carlson prefix adder |"
  Actually: rtl/math/math_bf16_exponent_adder.sv instantiates nothing; the entire computation is
            one behavioral statement:
              assign w_exp_sum_raw = {2'b0, i_exp_a} + {2'b0, i_exp_b} +
                                     {9'b0, i_norm_adjust} - 10'd127;
            (math_bf16_exponent_adder.md itself describes it correctly as "10-bit arithmetic".)
            The Han-Carlson claim may hold for the ieee754 fp16/fp32 cores (their RTL is not in
            this unit), but as a blanket "each format" statement it is false for bf16.
  Impact:   A reader believes the shared prefix-adder cores are reused uniformly and goes looking
            for a Han-Carlson instance in the bf16 exponent path that does not exist.
```

### 3. Parity-generator example in math_adder_basic.md cannot compile

```
[CONFIRMED] "Half Adder: Parity Generator" example is structurally illegal SystemVerilog
  File:     docs/markdown/RTLCommon/math_adder_basic.md
  Says:     "genvar i;
             generate
                 if (i == 0) begin
                     assign parity_chain[0] = data[0];
                 end else begin
                     math_adder_half u_parity ( .i_a(data[i]), .i_b(parity_chain[i-1]), ... );"
  Actually: A genvar used in a generate-if outside any for-generate has no value — the construct
            is illegal and will not elaborate. Additionally, "parity_chain" is never declared.
            A correct version needs "for (i = 1; i < 8; i++) begin : gen_parity" plus a declared
            "logic [7:0] parity_chain;".
  Impact:   Copy-paste fails at elaboration; this is presented as a teaching example for the
            simplest module in the library.
```

### 4. Brent-Kung page contradicts itself on forward-tree depth

```
[CONFIRMED] math_adder_brent_kung.md gives three different forward/reverse depth splits
  File:     docs/markdown/RTLCommon/math_adder_brent_kung.md
  Says:     Algorithm overview: "Forward Tree (log2(N) levels): ... Reverse Tree (log2(N)-1 levels)"
            Key Features: "Forward tree: log2(N) - 1 levels; these are the levels that contain
             black cells ... Prefix-network depth: 2 x log2(N) - 2 cell levels"
            and the ASCII "Prefix Network Structure (32-bit Example)" draws 5 forward depths
            (Depth 1-5) and 2 reverse depths (Depth 6-7), i.e. prefix depth 7.
  Actually: From the generated grouppg_032 network: black cells occupy prefix levels 1-4
            (pairs at L1, then 7_4-class at L2, 15_8-class at L3, 31_16 at L4) and gray fill-in
            occupies the rest; prefix depth = 8 = 2·log2(32)-2, matching the doc's own measured
            table ("32-bit | Prefix levels 8 | Total 10"). The overview's "log2(N) levels" for
            the forward tree is off by one, and the ASCII diagram matches neither.
  Impact:   A reader trying to reason about pipelining or retiming the prefix network gets two
            conflicting depth formulas on the same page.
```

### 5. Library overview omits the 64-bit Brent-Kung variant

```
[CONFIRMED] math_library.md Brent-Kung module list is incomplete
  File:     docs/markdown/RTLCommon/math_library.md
  Says:     "| **Brent-Kung** (parallel prefix) | `math_adder_brent_kung_{008,016,032}` + prefix
             cells ... |"
  Actually: rtl/math/math_adder_brent_kung_064.sv exists, and math_adder_brent_kung.md lists all
            four widths and explains the 64-bit variant is the final CPA of the 32-bit Dadda and
            Wallace multipliers.
  Impact:   Minor gap in the organizing map; the width exists and has a documented consumer.
```

### 6. addsub logic-depth formula disagrees with its own breakdown

```
[CONFIRMED] math_addsub.md: "2N + 2 levels" vs its own 17-level total for N=8
  File:     docs/markdown/RTLCommon/math_addsub.md
  Says:     "| **Logic Depth** | 2N + 2 levels (XOR + ripple carry chain) |"
            then: "1. XOR stage: 1 level ... 2. Carry chain: 16 levels (8 full adders × 2)
             3. **Total**: 17 levels"
  Actually: 2·8 + 2 = 18 ≠ 17. The RTL (one XOR stage feeding a chain of N full adders in
            rtl/math/math_addsub_full_nbit.sv) supports 2N+1 = 17, so the formula is the wrong
            one of the two.
  Impact:   Trivial off-by-one; only matters to someone comparing depth formulas across pages.
```

### 7. pg_chain "degenerates to half adder" at N=1 — it degenerates to a full adder

```
[CONFIRMED] math_adder_pg_chain.md width guideline is wrong at the minimum
  File:     docs/markdown/RTLCommon/math_adder_pg_chain.md
  Says:     "**Minimum**: 1 bit (degenerates to half adder)"
  Actually: At N=1 the RTL gives ow_sum[0] = p[0] ^ w_c[0] = i_a ^ i_b ^ i_c and
            ow_carry = g[0] | (p[0] & i_c) — exactly a full adder (it has a carry input, which a
            half adder by definition lacks). The ripple-carry page gets this right
            ("degenerates to single full adder").
  Impact:   Trivial factual slip.
```

### 8. Documented modules with no RTL in this package — unverifiable

```
[SUSPECTED] Several modules documented with full port/parameter tables are absent from RTL.sv
  File:     docs/markdown/RTLCommon/math_adder_basic.md (math_adder_half, math_adder_full_nbit),
            docs/markdown/RTLCommon/math_adder_carry_save.md (math_adder_carry_save_nbit),
            docs/markdown/RTLCommon/math_library.md (math_subtractor_{full,half,full_nbit,
             ripple_carry,carry_lookahead})
  Says:     e.g. "math_adder_carry_save_nbit #(parameter int N = 4) (input logic [N-1:0] i_c, ...
             output logic [N-1:0] ow_carry ...)" — full interface tables.
  Actually: None of these appear in the provided ground-truth RTL. Note the prefix cells
            math_adder_brent_kung_pg, math_prefix_cell and math_prefix_cell_gray are likewise
            absent even though they are *instantiated* by RTL that is present — so absence from
            this package does not prove absence from the repo, and I could not confirm existence
            or nonexistence for any of them from the material given.
  Impact:   If any of these were never written, their pages document vapor; if they exist, no
            harm. The author should confirm each exists with the documented interface. (Note the
            provided Han-Carlson and Brent-Kung adders will not elaborate as packaged, since the
            pg/prefix cell definitions are missing from RTL.sv.)
```

### 9. bf16 adder doc's special-case priority block omits the zero-operand branches

```
[CONFIRMED] math_bf16_adder.md "Special Case Priority" code is an incomplete quote of the RTL
  File:     docs/markdown/RTLCommon/math_bf16_adder.md
  Says:     The always_comb block shows the priority chain as: NaN -> any_inf -> sum_is_zero ->
             overflow -> underflow (5 cases).
  Actually: rtl/math/math_bf16_adder.sv has 8 branches: after any_inf it checks
            "r4_a_eff_zero && r4_b_eff_zero" (result {sign_a & sign_b, 0x00, 0x00}), then
            "r4_a_eff_zero" alone, then "r4_b_eff_zero" alone, before sum_is_zero/overflow/
            underflow. The zero-input handling is only described in prose elsewhere on the page
            (the "Sign of Zero" section matches the RTL).
  Impact:   Low — the branches are mutually exclusive so no stated behavior is wrong, but the
            block is presented as the implementation and a reader comparing with the RTL will
            find three missing branches.
```

---

## POSSIBLE RTL BUGS

**1. `math_bf16_adder`: negative adjusted exponent asserts the overflow flag, and the result mux returns +inf instead of FTZ zero.** In the normalization stage:

```systemverilog
wire w_exp_overflow  = w_exp_adjusted[8] || (w_exp_adjusted[7:0] >= 8'hFF);
wire w_exp_underflow = w_exp_adjusted[8] || (w_exp_adjusted[7:0] == 8'h00);
```

`w_exp_adjusted` is 9-bit two's complement, so bit 8 means "negative" for the subtraction path (`{1'b0, r3_exp_l} - {5'b0, w_norm_shift_amt}`) but "≥256" for the addition path — one bit encodes both. For any result whose true exponent goes negative (subnormal result from catastrophic cancellation), **both** flags assert, and the result mux checks `w_final_overflow` *before* `r4_exp_underflow`, so the output is infinity with `ow_overflow=1`. Concrete reachable case: two normals with exp_l = 1 whose mantissas differ by 1 ULP → difference = 2⁻¹³³ (subnormal; FTZ requires +0 with `ow_underflow=1`, which is what the doc describes). Trace: `w_mant_sum = 12'h008` → `w_lzc = 8` → shift = 7 → `w_exp_adjusted = 1 − 7 = −6 = 9'b1_1111_1010` → bit 8 set → overflow=1, underflow=1 → mux takes overflow → `ow_result = {sign, 8'hFF, 7'h00}` (+inf), `ow_overflow = 1`. The underflow branch should be checked first, or `w_exp_overflow` should be qualified with `~w_exp_adjusted[8]`/sign-aware comparison. Confidence: high by inspection; I could not run a simulation, so a directed test (exp_l=1, mantissas differing by 1 ULP) is recommended. The doc's description ("Underflow to zero (FTZ)") is the *correct intended* behavior — the RTL fails it.

**2. `shifter_barrel` (dependency): shift_amount == WIDTH returns the input unshifted in the no-wrap modes.** For the no-wrap cases the zero-check uses the modulo-reduced amount but the shift uses the raw amount:

```systemverilog
3'b001: data_out = (shift_amount_mod == 0) ? data : data >> shift_amount;
```

At WIDTH=8, shift_amount=8: `shift_amount_mod == 0` → output = `data`, but an 8-bit logical right shift by 8 should be 0. (Same structure at 3'b100; the wrap and arithmetic modes also reduce the amount modulo WIDTH, which is wrong for "no wrap" semantics at shift ≥ WIDTH.) Currently masked: the only instantiation here is in `math_bf16_adder` at WIDTH=11 with the amount clamped to ≤ 11, so `shift_amount_mod` is never 0 with a nonzero shift. Latent for any other caller at power-of-2 widths.

---

## Overall assessment

The two prefix-adder pages are the strongest in the unit: I independently recounted every black/gray cell and prefix stage in all four Brent-Kung and all six Han-Carlson generated networks, and the docs' measured tables match the RTL exactly, including the cell-count formulas (`N − log2(N) − 1` black, `N` gray) and the honest note that Brent-Kung beats Han-Carlson on cells at N=16. Module declarations, parameters, ports, and logic equations are accurate everywhere I could check them (full/half adders, ripple, pg_chain, addsub, bf16 exponent adder, bf16 adder datapath). The timing/frequency tables are now explicitly labeled as unsourced estimates, which addresses that known weakness. The serious defects are concentrated: the carry-save page's no-shift claim (Finding 1) is wrong, self-contradictory, self-falsifying via its own worked example, and brands the correct code as an anti-pattern — it needs a rewrite of its "Final Addition", examples, misconception callout, and pitfalls sections. The bf16 adder underflow bug (RTL, not doc) should be fixed before release since the documented FTZ behavior is what users will rely on. The remaining items are a broken teaching example, one overview overgeneralization, and minor nits.