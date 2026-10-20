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

# The Accumulator Rows: MAC and REDUCE

## Why a Wide Accumulator

`alu_infer_acc` holds the block's main state: a bank of `LINE_W/8` 32-bit
lanes (4 at `LINE_W = 32`). The float formats accumulate in fp32 and int8
in int32. A bf16×bf16 product is **exact** in fp32 (8 × 8 significand
bits fit in 24), so `math_bf16_fma` accumulates with one rounding per step
and the bank rounds to the element format only when a result is presented.
This is the production pattern (owner decision 2026-10-17, PRD §3).

## Structure

```text
issue --> [ MAC_LATENCY operand stages ] --> accumulate stage --> view --> port 3
           tag, A, B, imm, func_sel, acc_ctrl      |      ^
                                                   v      |
                                               accumulator bank
```

Every accumulator invocation — CLEAR, HOLD and DRAIN included — enters the
operand pipeline in issue order and reads the bank at the accumulate stage,
never at issue. A dependent chain is therefore correct at any
`MAC_LATENCY`, and it sustains one step per clock: the loop is the single
accumulate stage, and the operand stages sit ahead of it.

| Format | Lanes used | MAC update | REDUCE sum | REDUCE max |
|---|---|---|---|---|
| bf16 | 0 .. LINE_W/16-1 | `math_bf16_fma(a, b, acc)` | `fma(a, 1.0, acc)` | `math_fp32_max(acc, a)` |
| fp8 e4m3 | 0 .. LINE_W/8-1 | operands widened exactly to bf16, then as bf16 | as bf16 | as bf16 |
| fp32 | 0 .. LINE_W/32-1 | `math_ieee754_2008_fp32_fma(a, b, acc)` | `fma(a, 1.0, acc)` | `math_fp32_max(acc, a)` |
| int8 | 0 .. LINE_W/8-1 | `acc + a*b` (int32, wraps) | `acc + a` | `max(acc, a)` |

: Table 2.4: accumulate operation per format

The bank is shared across formats. Lanes a format does not use hold their
value; a program that changes format mid-layer issues CLEAR first.

## Why the Loop Stays Fused

The draft MAS described a split row: an exact-product stage, pipelined,
ahead of a one-cycle fp32 add in the loop. As built, the loop is the fused
library block. A 4-million-vector equivalence check of
`fp32_adder(exact_product, acc)` against `math_bf16_fma(a, b, acc)` found
24,987 differences. The two classes were a product that overflows fp32
against an infinite accumulator (the fused block returns the
accumulator, the split returns NaN), and subnormal accumulator
pass-through. The split would trade the library's numerics for a loop the
8×8 bf16 product barely lengthens. Depth goes into the operand stages
instead, where the integration flow can retime it into the product half.

## acc_ctrl

| `acc_ctrl` | Action |
|------------|--------|
| `HOLD` (00) | bank unchanged; present it |
| `ACCUMULATE` (01) | bank ← update (Table 2.4) per active lane; present the new bank |
| `CLEAR` (10) | bank ← the operation's identity: +0 for MAC and sum, −inf for max (int8: INT32_MIN) |
| `DRAIN` (11) | bank unchanged; present it (the layer's final read-out) |

: Table 2.5: accumulator actions

## Presentation (decision M7)

Every accumulator invocation retires one result line: the post-update bank
rounded to the element format. That is `math_fp32_to_bf16` for bf16 and
`math_fp32_to_fp8_e4m3` for fp8. fp32 presents the bank exactly. int8
presents `sat8(round(acc / 2^imm[4:0]))`, the requantize shift (round half
up), so an int8 layer drains to int8 without a separate pass. The bank
itself never rounds: the views are lossy, the state is not.

## REDUCE and the Cross-Lane Fold

REDUCE folds a span of lines into the bank. Each ACCUMULATE adds line A
(sum) or keeps its maximum (max), lane by lane; B is unused. CLEAR starts
a span and DRAIN reads it out. This is the PRD's roadmap item 1, which
unlocks softmax, layernorm and pooling.

A per-lane result still leaves `N` partial results. **`sub_op[1]` presents
the cross-lane fold**: the sum (or max) of the active lanes, in lane order
(`((l0 + l1) + l2) + l3`, fp32 adds), broadcast to every lane of the
result. The bank is unchanged, so a program can DRAIN the per-lane values
and the fold from the same span. Softmax uses it directly: REDUCE max with
fold gives the row maximum in every lane, ready for the subtract.

## Isolation Invariants

- The bank is read and written only by the accumulator rows (PRD §4
  invariant 2, extended from MAC to REDUCE).
- CLEAR or reset is the only way to re-initialize it, so a chain is
  reproducible from `{reset, acc_ctrl sequence, operand sequence}`.
- Outside the fold, lane `i` of the bank never sees lane `j`'s operands.

---

**Last Updated:** 2026-10-20
