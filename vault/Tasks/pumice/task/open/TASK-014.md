# TASK-014: the adaptive page modes need a disposition — retire mode 4, re-plumb mode 5

**Status:** open 2026-09-26  **Priority:** P3 — research/cleanup; the shipping
default no longer depends on either mode

Filed out of [[TASK-013]], which answered the question it was opened for and is
now closed. What remains is not a measurement but two decisions plus the
observability needed to make the second one safely.

## Context in one paragraph

Closing pages early is the largest runtime win on this controller (up to
+41.2%), and `fixed_open` (mode 3) captures all of it. The mechanism that
matters is the **background precharge gated on bank idle**
(`timeout_pre_req_o`), not a predictor and not auto-precharge. As of 2026-09-26
`PAGE_POLICY_CFG.policy_mode` resets to 3. Modes 4 and 5 are therefore no longer
on any critical path — which is exactly why they can be dealt with cleanly.

## 1. Retire mode 4 (`adapt_time`) — it is `fixed_open(tr_min)`

Measured: moving only `tr_min` moves the result, and it lands *exactly* on the
corresponding fixed point every time.

| config | `tr_min` | rd MB/s | equals |
|---|---|---|---|
| `adapt_time` | 2 | 436.8 | `fixed_open` TR=2 -> 436.8 |
| `adapt_time` | 8 | 338.5 | `fixed_open` TR=8 -> 338.5 |
| `adapt_time` | 16 | 327.7 | `fixed_open` TR=16 -> 327.7 |

The mistake counter is dominated by the held-too-long case, so TR decays
monotonically to the floor and stays. `r_mc` is also a single GLOBAL counter
driving all eight `r_tr[b]` from one decision, so `policy_scope=0`'s "per-bank
TR" cannot diverge and is a fiction that should not survive into any successor.

Retiring it costs nothing functional: **mode 3 IS its close path.** What comes
out is the mistake counter, `check_interval`, `tr_max`/`tr_step`, and the
`PAGE_ADAPT_CFG` register. Measure the area returned the way [[TASK-011]] did
for RBL, and keep `tr_init`/`tr_min` semantics for mode 3.

Do it the RBL way: remove, regenerate, gate, rebuild, and confirm streaming is
unchanged at 572.2-572.3 MB/s so the removal is provably inert.

## 2. Re-plumb mode 5 (`adapt_access`) to the background precharge

Mode 5 is **unproven and mis-plumbed, not disproven**, and it has two separate
problems that must not be conflated.

**(a) It drives the wrong mechanism.** `close_pred_o` feeds `ap_close_o`, i.e.
auto-precharge, which measures 4.9x the activations of a background precharge on
identical traffic (160,006 vs 32,400 ACT) and double the read latency. AP is
uncancellable: it commits at the column op, before it is known whether more
requests to that row are coming, whereas a background PRE fires only once the
bank goes idle and so spares rows with queued same-row requests. On a controller
whose value is FR-FCFS reordering to batch same-row columns, AP fights the
reordering that justifies the design. **Even a perfectly correct predictor
driving AP is bounded by a mechanism that loses.**

**PREMISE WARNING (2026-09-26): (b) below may be an ARTEFACT.** The char sim runs
at `FPGA_CLK_HZ = 100_000_000` and the board at 75 MHz, so every JEDEC timing is
1.33x more cycles in sim. That alone changes how many column ops an activation
serves, which is the ONLY thing mode 5 learns from. **Run the char sim at 75 MHz
and re-measure before doing any of (b)** -- see [[TASK-015]]. (a) is unaffected:
the mechanism argument against auto-precharge is a board-only measurement.

**(b) It also does not assert on hardware.** `PRE ~= ACT`, thrash falls only
100% -> 97% at best, against ~60% of activations converted in the DFI-loopback
sim on identical stimulus. Ruled out: run length (board engagement is 0% at
txn_scale 1 and 10, saturating at 3% from 100) and refresh rate
(non-monotonic — zero at BOTH extremes). The `ap_close_o` port itself is proven
good: mode 2 driving it returns ACT=160,002 / PRE=2.

**The change worth making:** have `close_pred_o` raise `timeout_pre_req_o` for a
predicted-dead row — close it as soon as the bank idles, without waiting out TR —
instead of driving `ap_close_o`. That keeps the idle-gate cancellation that makes
mode 3 fast while adding the per-row selectivity mode 5 was built for. It is the
only version of mode 5 that could beat `fixed_open`, and it makes (b) moot by
construction if the verdict is consumed at idle rather than at the column op.

Three candidates for (b) if it is chased directly instead, in order:

1. `close_pred_o[b] <= 1'b0` on EVERY fall, re-established only at the next ACT.
   Under real tRCD/tRAS the column op may issue before the verdict is live.
2. `r_col_cnt` reset discipline. Learning compares `r_col_cnt <= 2'd1` at the
   explicit PRE; if it does not clear per activation on hardware timing, every
   row looks multi-access and votes OPEN forever — exactly the observed
   `PRE ~= ACT`.
3. The `w_fall` claim window is ONE cycle, tuned against loopback timing. On the
   board a PRE lagging the fall further would misclassify explicit closes as AP
   closes and suppress learning entirely.

(1) and (3) are both "a timing assumption that holds in the loopback and not on
the board", the shape of every sim/board divergence in this controller so far.

## 3. Predictor observability — do this FIRST

**Three separate investigations in [[TASK-013]] had to infer predictor state
from bandwidth equality**: mode 4's TR decay (needed three board runs and a
floor sweep to establish what one readback would have shown), the refresh
hypothesis, and mode 5's non-assertion. There is no readback for `r_tr[0]`,
`close_pred_o`, or `r_col_cnt`.

Add a small stat block — `r_tr[0]`, a `close_pred_o` assert count, an AP-close
count. It is cheap, it unblocks every candidate above directly, and without it
any fix to mode 5 is verified the same indirect way that has already produced
one wrong conclusion in this area (see the corrected "AP datapath is proven
good" argument in [[TASK-013]], which was proven about the legacy `w_ap` path
and not about `ap_close_o` at all).

## Not in scope

Do not re-open the *idea* of per-row prediction on the strength of the sim
numbers. The loopback charges nothing for page management, so it cannot rank
paging policies at all; only the board can. Any claim about mode 5 needs board
evidence with the telemetry above.

Related: [[TASK-013]] (the campaign and every measurement quoted here),
[[TASK-011]] (RBL — the worked example of retiring a mode properly),
[[TASK-002]] (FR-FCFS reordering value, which AP undoes).
