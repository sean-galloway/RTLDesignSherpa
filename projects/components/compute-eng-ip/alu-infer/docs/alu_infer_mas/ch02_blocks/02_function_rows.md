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

# The Function Rows

Each row is one table entry. It takes the lanes of operand A (and B or the
immediate), computes every lane in parallel and independently, and returns
one result line. The `rtl/math` block named for a row is its
implementation. That block's structure, numerics and special-value
handling are documented in its rtl-math page and not restated here; this
chapter pins the row's wiring.

## Opcode Map

| Opcode | Row | Formats | Operands | Port |
|---|---|---|---|---|
| 0 | copy | all | A | comb |
| 1 | add | all | A, B | adder (bf16, fp32) / comb (int8, fp8) |
| 2 | sub | all | A, B | as add |
| 3 | mul | all | A, B | multiplier (bf16, fp32) / comb (int8, fp8) |
| 4 | mac | all | A, B, bank | accumulator |
| 5 | min / max (sub_op[0]) | all | A, B | comb |
| 6 | compare (sub_op[0]: B / imm) | all | A, B or imm | comb |
| 7 | relu | all | A | comb |
| 8 | reduce (sub_op[0]: sum / max; sub_op[1]: fold) | all | A, bank | accumulator |
| 9 | pwl | bf16 | A, LUT | comb |
| 10 | pwl_lut (sub_op[0]: write / read) | bf16 | A = entry, B[7:0] = index | comb |
| 11 | const | all | imm | comb |
| 12 | leaky-relu | bf16, fp32, fp8 | A | comb |
| 13 | gelu | bf16, fp32, fp8 | A | comb |
| 14 | sigmoid | bf16, fp32, fp8 | A | comb |
| 15 | silu | bf16, fp32, fp8 | A | comb |
| 16 | tanh | bf16, fp32, fp8 | A | comb |
| 17 | reciprocal | bf16 | A | comb |
| 18 | exp2 | bf16 | A | comb |
| 19 | log2 | bf16 | A | comb |
| 20 | log2-scale (qscale) | bf16 | A | comb |
| 21 | cvt (src = fmt, dst = sub_op) | library pairs | A (+ B) | comb |
| 22 | altfmt (bf16 <-> fp16 / e5m2) | bf16 | A (+ B) | comb |
| 23–31 | — | — | — | illegal |

: Table 2.2: the function rows

"All" means every format built in. A (format, opcode) pair outside this
table is illegal (Chapter 2.4).

## Elementwise Rows per Format

| Row | bf16 | int8 | fp32 | fp8 e4m3 |
|---|---|---|---|---|
| add / sub | `math_bf16_adder` (sub: B sign flipped) | saturating `a ± b` | `math_ieee754_2008_fp32_adder` | `math_fp8_e4m3_adder` |
| mul | `math_bf16_multiplier` | saturating `a × b` | `math_ieee754_2008_fp32_multiplier` | `math_fp8_e4m3_multiplier` |
| min / max | `math_bf16_min` / `_max` | signed compare | `math_fp32_min` / `_max` | `math_fp8_e4m3_min` / `_max` |
| compare | `math_bf16_comparator` (lt) | signed `a < b` | `math_fp32_comparator` | `math_fp8_e4m3_comparator` |
| relu | `math_bf16_relu` | `a < 0 ? 0 : a` | `math_fp32_relu` | `math_fp8_e4m3_relu` |
| const | `imm` | `imm[7:0]` | `{imm, 16'h0}` | `imm[7:0]` |

: Table 2.3: elementwise rows

## Per-Row Notes

**copy (0).** Operand A to the result line, in any format; useful for
moving lines and for test patterns.

**add / sub (1, 2).** Sub shares the adder with B's sign bit flipped (bf16,
fp32, fp8). The bf16 and fp32 adders are pipelined `ADDER_LATENCY` stages
and land on the adder port; the int8 and fp8 adders are combinational.
int8 saturates to [-128, 127] — the inference convention — and never
wraps.

**mul (3).** The bf16 and fp32 multipliers are combinational blocks
followed by `MUL_LATENCY` output stages. Those registers are retiming
candidates: the integration flow moves them into the multiplier. int8
saturates its 16-bit product.

**min / max (5).** `sub_op[0]` picks max. NaN semantics are each block's
own: the float blocks return the non-NaN operand (IEEE `minNum`/`maxNum`),
recorded at M1.

**compare (6).** Lane `i` of the mask is `A[i] < B[i]`, or
`A[i] < imm` when `sub_op[0]` is set. The mask is packed low in
`result_flags`, one bit per lane of the format (2, 4, 1 or 4 bits), and
`result_line` is zero. The immediate is the raw pattern of the format: a
bf16 pattern for bf16, widened exactly to fp32 for fp32, and `imm[7:0]`
for int8 and fp8 (M4).

**relu (7).** Negative lanes to zero; NaN passes per the block (M1).

**const (11).** The immediate broadcast into every lane of the format
(PRD roadmap item 3): a program builds a bias line without memory traffic.

## Activation and Scaling Rows

Opcodes 12–16 instantiate each format's library activation: leaky-relu
(alpha = 2^-`LEAKY_SHIFT`), gelu, sigmoid, silu, tanh, in bf16, fp32 and
fp8. Opcodes 17–20 are bf16 only, because those blocks exist only in bf16:
`math_bf16_reciprocal`, `math_bf16_exp2`, `math_bf16_log2` and
`math_bf16_log2_scale` (the quantization scale `2^ceil(log2 max)` of a max
value, as bf16).

These rows inherit the library's approximations unchanged. The gelu,
sigmoid, silu and tanh blocks are coarse piecewise forms (gelu, for
example, is a constant over the medium range). **The PWL row (Chapter 2.5)
is the accurate activation path.** It is what the PRD's roadmap item 2
asked for, and its error is bounded and measured. There is no divider
row: the PRD (roadmap, 2026-10-19) plans none, and exp followed by
reciprocal-multiply covers softmax's divide.

## What Every Row Shares

- **Lane independence.** Lane `i` of a result never depends on lane `j`
  (PRD §4 invariant 1). The accumulator rows' fold sub-op is the one
  deliberate exception (Chapter 2.3).
- **Natural speed, joined by tag.** A row does not pad itself to match
  slower ones; its port carries the tag and the FIFO keeps order (Chapter
  2.4).
- **FTZ.** Every library block runs at its default `SUBNORMAL_SUPPORT = 0`:
  subnormal inputs flush to zero (M3).

---

**Last Updated:** 2026-10-20
