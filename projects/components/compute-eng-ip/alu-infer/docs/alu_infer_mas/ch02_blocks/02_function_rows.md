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

# The Seven Function Rows

Each row is one RTL table entry: same lanes in, two lanes out, no state.
The `rtl/math` block named per row is the implementation base — its
internal structure, pipeline behavior, and special-value handling are
documented in its own rtl-math page and are not restated here (one
source per fact). What this chapter pins is the row's *wiring* into the
ALU: operands, lane routing, and the one or two integration decisions
the block does not make.

## Row Summary

| Opcode | Row | Library block | Operands | Notes |
|--------|-----|---------------|----------|-------|
| 0 | copy | wires (bypass) | 1 line | passthrough; latency-free |
| 1 | add | `math_bf16_adder` | 2 lines | per-lane |
| 2 | sub | `math_bf16_adder` | 2 lines | sign-flip B's sign bit pre-add (see below) |
| 3 | mul | `math_bf16_multiplier` | 2 lines | mantissa_mult + exponent_adder inside |
| 4 | mac | `math_bf16_fma` | 2 lines + acc | the workhorse; see `alu_infer_acc` chapter |
| 5 | min / max | `math_bf16_min` / `math_bf16_max` | 2 lines | sub-op selects; NaN semantics per M1 |
| 6 | compare / threshold | `math_bf16_comparator` | 2 lines or line + imm | mask bits, not values; imm encoding M4 |
| 7 | relu | `math_bf16_relu` | 1 line | per-lane; NaN passthrough per M1 |

: Table 2.2: the v1 function rows (normative list in PRD §3)

## Per-Row Notes

**copy (opcode 0).** A bypass lane from operand A's lanes to the result
select. It exists so the FSM can move lines through the ALU without a
function — useful for drain and test patterns. No library block, no
latency, no flags.

**add / sub (opcodes 1–2).** One `math_bf16_adder` serves both rows.
The sub row flips operand B's sign bit before the adder — the standard
sign-magnitude subtract — so the two rows share one block instance
selected by the row decode. Rounding is the library's RNE; the adder's
IEEE exception outputs are observable inside the row and are *not*
forwarded in v1 (open item M2).

**mul (opcode 3).** `math_bf16_multiplier` (its `mantissa_mult` and
`exponent_adder` children do the field work). "Low half" is meaningless
in floating point — the product is the rounded bf16 result, per the
PRD's bf16 reframing of the cell PRD's integer "low half" row.

**mac (opcode 4).** `math_bf16_fma`, consuming the accumulator bank;
the row's micro-architecture *is* the next chapter.

**min / max (opcode 5).** Two library blocks (`math_bf16_min`,
`math_bf16_max`) behind the sub-op bit; both compare through
`math_bf16_comparator`. The only open question with hardware
consequences is NaN propagation (IEEE `minNum` quiet-NaN semantics vs
the inference "ignore NaN" convention) — the library blocks' existing
semantics decide, and the choice is recorded at M1 so the golden model
agrees.

**compare / threshold (opcode 6).** `math_bf16_comparator` per lane,
comparing A against B or against `threshold_imm` (sub-op selects). The
row's output is **mask bits, not values** — each lane contributes one
bit, packed by the line composer into `result_flags` (format closed:
one bit per lane, packed low — M5).
`threshold_imm` carries a raw bf16 bit pattern in the simplest encoding
(alternative: small int compared after conversion — M4).

**relu (opcode 7).** `math_bf16_relu` per lane: negative lanes go to
+0, positives and the sign of zero pass per the library's contract.
NaN passthrough is the library default and is carried at M1 so the
golden model states it explicitly.

## What Every Row Shares

- Two lanes computed **in parallel, independently** — lane *i* of a
  result never depends on lane *j* (PRD §4 invariant 1). This is what
  lets the testbench check a lane against a scalar golden reference.
- **Presentation, not padding.** As the library ships, every row
  except add/sub is one combinational cloud (latency 0), and the adder
  carries optional `PIPE_STAGE_1..4` (latency 0–4). The ALU does not
  force fast rows through deep pipe stages to match: each row computes
  at its natural speed, and `alu_infer_pipe`'s alignment timer delays
  presentation to the common `ROW_LATENCY`, in issue order (Chapter 3).
  A row whose timing genuinely needs depth — the mac row's exact-product
  pipe, a multiplier restructured for the integration clock — carries
  real stages instead; that work belongs to `rtl/math` (the `PIPE_STAGE`
  family precedent) and does not change this block's contract.
- Growth rows (gelu, sigmoid, silu, tanh, leaky-relu, reciprocal,
  divide, conversions — PRD §3 growth list) are additional children of
  `alu_infer_rows` behind free opcodes, added without touching the
  handshake or the select width.

---

**Last Updated:** 2026-10-19
