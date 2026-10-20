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

# The Issue Seam

The seam between the issuer and this block is the ALU's whole external
surface, plus one status output. The issuer is the tetrad's **gatling**
core (owner ruling 2026-10-19): a context's program presents an
invocation's operands and function, and takes the result line back. Which
Xcell instructions and cell glue drive these signals is gatling-MAS scope.
This chapter fixes what the ALU sees.

## Signal Contract

| Signal | Dir (ALU view) | Width | Semantics |
|--------|----------------|-------|-----------|
| `op_line_a` | in | `LINE_W` | operand line A; captured at the issue edge together with B (owner ruling 2026-10-17: two ops scheduled in the same clock finish at the same time) |
| `op_line_b` | in | `LINE_W` | operand line B (unused by unary rows; the PWL index, conversion part select) |
| `threshold_imm` | in | 16 | immediate: compare threshold, const value, quantize scale, int8 requantize shift (`[4:0]`) |
| `func_sel` | in | 9 | `{fmt[8:7], sub_op[6:5], opcode[4:0]}` — sampled at issue |
| `acc_ctrl` | in | 2 | accumulator action for MAC and REDUCE (Table 2.5); ignored by other rows |
| `valid` | in | 1 | the issuer presents an invocation; all inputs stable while `valid && !ready` |
| `ready` | out | 1 | the tag FIFO has room (or the head retires this cycle) |
| `result_valid` | out | 1 | the head result is offered; held with stable data until consumed |
| `result_ready` | in | 1 | the issuer consumes the offered result |
| `result_line` | out | `LINE_W` | the result, one per invocation, in issue order |
| `result_flags` | out | `LINE_W` | compare mask, one bit per lane packed low (M5); zero otherwise |
| `err_opcode` | out | 1 | pulses on the issue edge of an illegal `func_sel` (status, not flow control) |
| `clk`, `aresetn` | in | 1 | single clock, asynchronous active-low reset |

: Table 3.1: issue-seam signals

An **issue** is a rising edge with `valid && ready`; a **retire** is a
rising edge with `result_valid && result_ready`.

## Handshake Rules

1. **Issue is `valid && ready`.** `ready` is high whenever the FIFO has
   room, so the issuer may present a new invocation **every clock** (II=1).
   It falls only once `PIPE_DEPTH` invocations are in flight behind a
   stalled consumer.
2. **Retire is `result_valid && result_ready`, strictly in issue order.**
   Each result is offered at its port's natural latency (Table 2.6) and
   never before every earlier invocation has retired. A stalled consumer
   holds `result_valid` with stable data; results behind it wait in their
   own entries.
3. **Elastic end to end.** There is no alignment state to freeze: entries
   hold their arrivals indefinitely, and when `result_ready` returns, the
   head retires and the rest drain one per cycle.
4. **In order by construction.** The issuer pairs result N with invocation
   N by counting. The 8-bit tags are internal and never on the seam (owner
   ruling 2026-10-18).
5. **Config sampled at issue.** `func_sel`, `acc_ctrl` and the immediate
   travel with the invocation, so the issuer may change them for the next
   issue at once.
6. **Every issue retires.** Illegal invocations, CLEAR, and PWL table
   writes all retire one line (zero for the illegal and the writes).
7. **Scheduler-paced feedback** (owner ruling 2026-10-17). Where results
   feed back — the accumulator chain, a program re-presenting a result as
   an operand — the issuer owns the pace. The ALU makes no autonomous
   pacing decisions. Because the accumulate loop is one cycle, a
   dependent MAC or REDUCE chain may be issued every clock.

### Waveform 3.1: Elastic handshake — natural latency, output stall, ready stays high

![Waveform 3.1: elastic handshake](../assets/wavedrom/wvf_3_1_invocation_handshake.png)

Two combinational invocations (MUL at `MUL_LATENCY = 0`, then RELU). The
MUL issued at n is offered at n+1 and the RELU lands behind it. The
consumer stalls from n+2 to n+4: the head holds `r(MUL)` with stable data
and **`ready` stays high**, because a two-entry backup is nowhere near
`PIPE_DEPTH`. The consumer accepts at n+5 and n+6.

### Waveform 3.2: Back-to-back issue — mixed latencies, in-order results

![Waveform 3.2: back-to-back issue](../assets/wavedrom/wvf_3_2_back_to_back.png)

MUL, ADD and RELU on consecutive clocks with the output draining. The MUL
retires at n+1. The head then belongs to the ADD, whose adder port lands
at n+5 (`ADDER_LATENCY = 3`); `result_valid` dips while the RELU, computed
long before, waits behind it. ADD retires at n+5 and RELU right after.
No row carries padded stages.

## Boundary Notes

- **Configuration.** Cell configuration arrives in-band on delta and
  gatling never originates config traffic (gatling PRD §1). The ALU sees
  configuration only as the per-invocation `func_sel` / `acc_ctrl` /
  immediate. The PWL table is loaded through the seam (Chapter 2.5).
- **Observability.** Ocelus owns it; the ALU has no monitor taps. The
  accumulator is readable through DRAIN and the PWL table through
  `OP_PWL_LUT` read, so no debug port is needed.

---

**Last Updated:** 2026-10-20
