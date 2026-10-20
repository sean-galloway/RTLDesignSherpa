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

# Decode and Result Ports

## Decode (`alu_infer_decode`)

A combinational check of `func_sel` against Table 2.2 and the build's
`EN_*` parameters. It returns `legal` and the result port. An invocation
is **illegal** when its opcode is unassigned (23–31), its format is not
defined for the row (an int8 activation, a PWL in fp32, reciprocal in fp8),
its conversion pair has no library converter, or its format or family is
built out.

An illegal invocation is not dropped. It routes to the combinational port
with a zero line and zero flags and **retires its slot in order** (owner
ruling 2026-10-17): the pipeline never deadlocks and gatling's count
pairing never breaks. On its issue edge `err_opcode` pulses for one cycle.
That is a status output for the cell's error IRQ, not seam flow control
(PRD §4: the seam carries no error signal).

## The Four Result Ports

| Port | Rows | Latency after the issue edge | Implementation |
|---|---|---|---|
| 0 combinational | copy, min/max, compare, relu, const, int8 and fp8 arithmetic, fp32 non-arithmetic, activations, PWL, conversions, illegal | 0 (written at the issue edge) | per-format result mux in `alu_infer_rows` |
| 1 adder | bf16 and fp32 add/sub | `ADDER_LATENCY` | library adder pipes; the tag and format ride an `alu_infer_delay` alongside |
| 2 multiplier | bf16 and fp32 mul | `MUL_LATENCY` | combinational multiplier, then `alu_infer_delay` of {tag, product} |
| 3 accumulator | MAC, REDUCE | `MAC_LATENCY` | `alu_infer_acc` (Chapter 2.3) |

: Table 2.6: result ports

Each port carries `{valid, tag, line, flags}`. Within a port, results are
in issue order. Across ports, several may land in the same cycle, each in
its own FIFO entry.

## The Tag FIFO and Arrival Join (`alu_infer_pipe`)

Owner ruling 2026-10-18: each issue takes an 8-bit tag, a FIFO tracks the
tags in flight, and a result is offered only when every op of its tag
group has arrived. As built:

- A free-running counter assigns the tag at issue, and the FIFO allocates
  the tail entry `{tag, pending}`.
- Each port that lands searches the entries for its tag (unique while in
  flight: `PIPE_DEPTH` ≤ 16 against a 256-value space) and fills
  `{line, flags, arrived}`. A port landing in its own issue cycle (latency
  0) writes the entry being allocated.
- The head is offered when it has arrived. A fast result behind a slow one
  waits at the head (owner ruling: following ops align with or after the
  earlier slower operation).
- `ready` is high while the FIFO has a free entry, or when the head
  retires this cycle. A stalled consumer blocks issue only once
  `PIPE_DEPTH` invocations are in flight.

**Tag groups.** The seam issues one `func_sel` per invocation, so a tag
group is one op and the join waits for one arrival. A multi-op group needs
a seam that issues several ops at once, which no document defines yet; the
per-port tag compare is the mechanism that group would use.

---

**Last Updated:** 2026-10-20
