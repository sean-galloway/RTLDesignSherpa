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

# The Compute Cycle, per Opcode Class

Every invocation is the same three beats — **present, compute, retire** —
but under the elastic handshake (Chapter 3) the beats of consecutive
invocations overlap: while one computes, the next is presented and the
previous retires. This chapter walks each class as if it were alone; the
overlap rules at the end apply to all of them together.

## Unary Rows (copy, relu, activations, PWL, const)

The issuer presents line A (const uses only the immediate). Every lane is
computed in parallel and the result lands on the combinational port at the
issue edge, so it is offered the next cycle.

## Binary Rows (add, sub, mul, min/max, compare)

Lines A and B arrive in the same clock (owner ruling 2026-10-17), and the
row pairs lane `i` of A with lane `i` of B. bf16 and fp32 add/sub land
`ADDER_LATENCY` cycles later, bf16 and fp32 mul `MUL_LATENCY` cycles later,
and everything else at the issue edge. Compare packs its mask into
`result_flags` and returns a zero `result_line`.

## Conversions

Narrowing conversions consume both lines and pack them into one result;
widening conversions consume one line and select the part with `B[1:0]`
(Chapter 2.6). All land at the issue edge.

## MAC and REDUCE (the chains that matter)

An accumulator invocation enters the operand pipeline and reaches the
accumulate stage `MAC_LATENCY` cycles later, where `acc_ctrl` chooses the
action:

1. **CLEAR** starts a layer or span: the bank takes the operation's
   identity (+0, or −inf for max). The invocation flows through like any
   other and retires the cleared view, so count pairing holds.
2. **ACCUMULATE** per step: MAC adds `a × b` (fused, one rounding), REDUCE
   adds `a` or keeps the maximum. The result line is the post-update bank
   in the element format (M7).
3. **DRAIN** reads out the final values without changing the bank. With
   REDUCE's `sub_op[1]` it presents the cross-lane fold instead.

### Waveform 4.1: MAC chain — clear, three accumulates, drain

![Waveform 4.1: MAC chain](../assets/wavedrom/wvf_4_1_mac_chain.png)

At `MAC_LATENCY = 0` each step is offered the cycle after its issue. A
deeper `MAC_LATENCY` delays every view by the same amount and keeps one
step per clock, because the loop is the accumulate stage alone. The
testbench proves both at `MAC_LATENCY` 0 and 2 on a 104-to-512-step chain
(Chapter 5).

## Overlapping Invocations

The pipeline never inserts a stall of its own. A MUL, a REDUCE and a PWL
may issue on consecutive clocks, all in flight together, retiring in issue
order as each one's port lands. Three consequences:

- **No drain logic.** Switching opcode or format mid-stream costs nothing:
  retirement is in issue order regardless of port latency.
- **The issuer pairs results by counting.** No tags on the seam.
- **Idle is a hold.** When `valid` drops, in-flight invocations drain, the
  last result holds until consumed, and the bank holds.

---

**Last Updated:** 2026-10-20
