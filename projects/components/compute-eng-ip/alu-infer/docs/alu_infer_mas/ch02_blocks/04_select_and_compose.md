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

# Result Select and Line Composer

## Result Select (`alu_infer_select`)

A mode mux, not an arbiter: `y = row[func_sel.opcode]`. The decode is a
`unique case` on `func_sel.opcode` with exactly the seven row outputs of
Table 2.2 as the case arms and no default path to a row — an opcode in
the 8–31 growth space selects the copy row's output only in a debug
configuration; in the shipped build an out-of-range opcode raises the
cell's error IRQ through the status path rather than producing a real
result (the cell PRD §8 error hook; the exact signaling is cell-RTL
scope). Owner ruling 2026-10-17: the errored invocation **still retires
its slot** with a don't-care result line — the elastic pipeline never
deadlocks and the FSM's count pairing never breaks. Sub-op bits travel with the row: min/max selection is resolved
inside `row_minmax`'s own decode, compare/threshold's operand choice
inside `row_compare` — the select mux itself keys on opcode only.

This is the deliberate anti-pest decision of the design: because the
select is a port-driven mux, there is no arbitration state, no fairness,
no starvation — and the house-style block diagram correctly shows a
plain box, not a trapezium.

## Line Composer (`alu_infer_compose`)

Two jobs. For every row except mac: pack the selected row's two bf16
lanes back into one 32-bit line — lane 0 to bits [15:0], lane 1 to bits
[31:16] (order fixed at MAS level so testbenches and the golden model
agree with the cell PRD's memory layout). For mac: the same packing
after the fp32→bf16 RNE rounding that presents the accumulator (Chapter
2.3, decision M7). The composer is also where `result_flags` is
assembled for opcode 6: one mask bit per lane, packed into the flags
field whose exact format is open item M5.

## Registered Config

`func_sel` and `acc_ctrl` are sampled at the issue edge (`valid &&
ready`), and the invocation runs on the sampled copy — so the FSM may
present the next `func_sel` while the current invocation computes. The
registered-config flop is the block's only config state besides the
accumulator; reset clears it (Chapter 2.1).

---

**Last Updated:** 2026-10-19
