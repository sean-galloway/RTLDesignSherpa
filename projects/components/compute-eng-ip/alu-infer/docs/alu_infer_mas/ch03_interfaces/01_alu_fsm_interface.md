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

# The ALU↔FSM Interface

The seam between the cell's execution FSM and this block. It is the
entire external surface of the ALU: the FSM owns sequencing, memories,
and the credit loop, and reaches the ALU only through these signals plus
clock and reset.

## Signal Contract

| Signal | Dir (ALU view) | Width | Semantics |
|--------|----------------|-------|-----------|
| `op_line_a` | in | `LINE_W` | operand line A (the function's `OP_LINES` count is across both ports: 1 for copy/relu, the A+B pair for binary/mac) — presented together with `op_line_b` and captured at the issue edge; owner ruling 2026-10-17: two ops scheduled in the same clock finish at the same time |
| `op_line_b` | in | `LINE_W` | operand line B (idle for unary rows) |
| `threshold_imm` | in | 16 | bf16 immediate for opcode 6 |
| `func_sel` | in | 9 | {opcode[4:0], sub_op[6:5], reserved[8:7]} — sampled at issue |
| `acc_ctrl` | in | 2 | accumulator action for a mac invocation (Table 2.3) |
| `valid` | in | 1 | FSM presents an invocation; operands and config stay stable while `valid` is high and `ready` is low |
| `ready` | out | 1 | the ALU can accept an invocation at this edge — high in every cycle that has room (sustained, that is every clock) and low only when a downstream stall backs up into the block |
| `result_valid` | out | 1 | a result is offered; stays high with stable data until consumed |
| `result_ready` | in | 1 | FSM consumes the offered result |
| `result_line` | out | `LINE_W` | the offered result line — one per invocation, in issue order |
| `result_flags` | out | `LINE_W` | opcode-6 mask — one bit per lane, packed low (M5 closed by owner ruling 2026-10-17); zero otherwise |
| `clk`, `aresetn` | in | 1 | house single clock, async active-low reset |

: Table 3.1: ALU↔FSM signals

An **issue** is a rising edge with `valid && ready`; a **retire** is a
rising edge with `result_valid && result_ready`. (The `accept` of
pre-v0.6 notes is exactly the issue event, not a pin.) `OP_LINES` (cell
PRD §7) is the per-function operand-line count — 1 for copy/relu (the A
line only), 2 for the binary rows and mac (the A line and the B line) —
and the two lines arrive **in the same clock** and are captured at the
issue edge; the count never appears as a beat sequence on this
interface.

## Handshake Rules

1. **Issue is `valid && ready`.** The invocation enters the selected
   row's pipeline only when both are high at the edge. `ready` is high
   whenever the block has room, so the FSM may present a new invocation
   **every clock** (II=1); it deasserts only under downstream
   backpressure, and while it is low the FSM holds `valid`, the operand
   lines, `func_sel`, and `acc_ctrl` stable — the standard valid/ready
   contract.
2. **Retire is `result_valid && result_ready`, strictly in issue
   order.** Each result is offered at its row's natural latency —
   combinational rows (copy, mul, min/max, compare, relu, mac) in the
   cycle after the issue edge, add/sub `ADDER_LATENCY` cycles after —
   never before every op of its tag group has arrived, and never
   overtaking an earlier invocation: a fast row behind a slow one waits
   at the FIFO head. When `result_ready` is low, `result_valid` holds
   with stable data and the results behind it wait in order — no loss,
   no reorder, no tags on the seam.
3. **The pipeline is elastic end to end.** Every stage boundary obeys
   valid/ready, and the tag FIFO is what makes it natural: a stall at
   the result port leaves the head entry offered with stable data while
   rows behind it keep landing in their own entries — issue remains
   open until the FIFO is *genuinely full* (`PIPE_DEPTH` in flight),
   and only then does `ready` fall. There is no alignment state to
   freeze: entries hold their arrivals indefinitely. When
   `result_ready` returns, the head retires and the entries behind it
   drain in order at one per cycle; issue resumes the moment an entry
   frees.
4. **In order by construction.** The tag FIFO retires in issue order,
   so the FSM pairs result N with invocation N by counting. The 8-bit
   tags are internal to the block (owner ruling 2026-10-18): they never
   appear on this seam, whose flow control is exactly the two
   valid/ready pairs. Quick rows compute in parallel at their natural
   speed and align at the join — `alu_infer_pipe` is a tag FIFO, **not**
   a bank of padded pipe stages (owner direction 2026-10-17/18).
5. **Config sampled at issue.** `func_sel` and `acc_ctrl` are sampled
   at the issue edge and travel with the invocation through the
   pipeline, so the FSM may change them for the next issue immediately.
6. **No error signal on this interface in v1.** An out-of-range opcode
   is a cell-level error (Chapter 2.4); the library blocks' IEEE
   exception outputs are not forwarded (open item M2).

The one place uniform latency is *engineered* rather than padded is
opcode 4: a dependent MAC chain feeds back through the accumulator, so
its sustained rate is set by the feedback loop's latency, not the issue
rate. The mac row is therefore split — pipelined exact-fp32-product
stage(s) ahead, single-cycle fp32 accumulate stage in the feedback
path — so a chain sustains II=1 with the output draining (Chapter 2.3).
**Scheduler-paced feedback** (owner ruling 2026-10-17): whenever
results feed back — opcode 4's chain today, any future recurrence —
the scheduler owns the pace entirely; it shapes the `valid` stream and
obeys `ready`, and the ALU makes no autonomous pacing decisions. The
single-cycle accumulate exists so that scheduler-chosen II=1 is
sustainable.

### Waveform 3.1: Elastic handshake — natural latency, output stall, ready stays high

![Waveform 3.1: elastic handshake](../assets/wavedrom/wvf_3_1_invocation_handshake.png)

Two invocations ride the elastic protocol end to end. Both are
combinational rows: the MUL issued at n is offered one cycle later
(n+1), the RELU issued at n+1 lands at n+2 — each taking its 8-bit tag
(t0, t1) at issue. The consumer stalls from n+2 to n+4: the head holds
`r(MUL)` with stable data, the RELU waits behind it in its own FIFO
entry, and **`ready` stays high throughout** — with `PIPE_DEPTH`
entries, a two-entry backup is nowhere near full, so the input side
never feels the stall. The consumer accepts at n+5 (MUL retires) and
n+6 (the waiting RELU retires immediately after). Operands and config
are stable from `valid` to issue; both operand lines are captured at
the issue edge.

### Waveform 3.2: Back-to-back issue — mixed latencies, in-order results

![Waveform 3.2: back-to-back issue](../assets/wavedrom/wvf_3_2_back_to_back.png)

Three invocations (MUL, ADD, RELU) issue on consecutive clocks with the
output draining. The MUL (combinational) retires at n+1. The head then
belongs to the ADD, whose pipelined row presents at n+5
(`ADDER_LATENCY = 3`); `result_valid` dips while the faster results
behind it — the RELU, computed at n+3 — wait at the join. ADD retires
at n+5, RELU immediately after. This is the owner ruling of 2026-10-18
in one picture: following ops are delayed to align with or after the
earlier slower operation, and no row carries padded stages to hide the
difference.

## Boundary Notes

- **Config plane.** The cell PRD's §7 register map (`FUNC_SEL`,
  `OP_LINES`, …) is AXIL and cell-RTL scope; this block sees config
  only as the registered `func_sel`/`acc_ctrl` inputs above. The
  in-band `cfg` packets that write those registers at layer boundaries
  travel with the delta traffic and are demuxed by the cell, never by
  this block.
- **Tetrad control core.** The kestrel-class per-tetrad core reads cell
  status and IRQs and exercises operational registers over the AXIL
  plane (alu-infer PRD §5; TILE_SPEC §11.13); it has no direct signals
  here by construction.

---

**Last Updated:** 2026-10-17
