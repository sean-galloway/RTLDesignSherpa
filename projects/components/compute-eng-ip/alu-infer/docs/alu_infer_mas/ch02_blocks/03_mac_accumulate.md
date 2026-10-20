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

# The FP32 MAC Accumulator

## Why fp32

`alu_infer_acc` is the block's only state, and it exists because of one
numerical fact: a bf16×bf16 product is **exact** in fp32 — 8 significand
bits times 8 significand bits is 16, well inside fp32's 24 — so a fused
multiply-add can accumulate inference layers in fp32 and only round to
bf16 when a result line is presented. bf16 accumulate would wrap every
operation and drift over a long chain; fp32 accumulate with one RNE
rounding at presentation is the production pattern (TPU-class
accelerators do exactly this) and is the owner decision of 2026-10-17
recorded in PRD §3.

## Structure

One bank, `N_LANES` (2) fp32 accumulator registers, each private to its
lane. `row_mac` feeds the bank and reads it back through
`math_bf16_fma`: `acc[i] <= fp32( a[i] × b[i] ) + acc[i]`, with the
fused single rounding the FMA block provides. The bank's only control
is `acc_ctrl[1:0]` (encoding in Chapter 6):

| `acc_ctrl` | Action |
|------------|--------|
| `HOLD` | acc unchanged (default) |
| `CLEAR` | acc ← +0.0 in every lane (layer boundary) |
| `ACCUMULATE` | acc ← fma(a, b, acc) per lane (a mac invocation) |
| `DRAIN` | present acc rounded to bf16; acc unchanged |

: Table 2.3: accumulator actions

## The Loop-Carried Dependence (why the row is split)

A dependent MAC chain is a recurrence: step *k* reads the accumulator
that step *k−1* wrote. Issue rate does not set the chain's speed — the
**feedback loop's latency** does. If the whole FMA were pushed through
an 8-stage pipeline, the chain would run at one step per 8 clocks no
matter how fast issues arrive. The row is therefore split:

- **Product stage(s)** — the bf16 multiply, whose fp32 product is
  exact — pipelined as deep as the integration clock wants (§7 growth).
  Feed-forward, so back-to-back invocations sustain II=1 regardless of
  depth; the tag FIFO absorbs the depth unchanged.
- **Accumulate stage** — one fp32 add in the feedback path,
  single-cycle. The chain closes in one clock: one fused accumulate
  per lane per cycle, sustained.

The product pipeline and the single-cycle accumulate also compose with
the tag-join contract: the bf16 view of step *k* retires in issue order
at the row's natural latency, like every other row.

## Presentation Semantics (MAS decision M7)

The PRD's interface contract says every v1 row produces one result line
per invocation, and this specification decides what a mac invocation
presents: **the post-update accumulator, rounded to bf16, as the result
line** — a running, observable accumulator view. `DRAIN` then means
"present without accumulating," which is how a layer's final values are
read out without a following accumulate. Accumulation itself stays in
fp32 whatever the presentation; the bf16 view is lossy but the state is
not. (This is the MAS reading of PRD §4's "one line per invocation";
flagged M7 in Chapter 6 so the owner can veto.)

## Isolation Invariants

- The bank is readable and writable **only** by `row_mac` (PRD §4
  invariant 2) — no other row's datapath crosses it.
- `CLEAR` is the only way to zero it; reset clears it; nothing else
  disturbs it, so a layer's accumulation chain is reproducible from
  `{reset, acc_ctrl sequence, operand sequence}` alone.
- Because the bank is per-lane, lane independence (PRD §4 invariant 1)
  survives mac: lane *i*'s accumulator never sees lane *j*'s operands.

The accumulator chain's cycle-level timing appears in Chapter 4
(Waveform 4.1); verification of long chains and clear/hold corners is
Chapter 5.

---

**Last Updated:** 2026-10-19
