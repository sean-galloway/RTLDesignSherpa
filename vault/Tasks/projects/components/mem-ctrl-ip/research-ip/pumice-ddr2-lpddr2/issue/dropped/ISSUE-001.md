# ISSUE-001: read latency is ~2x LiteDRAM's, and it caps small-burst reads
> **Was `PUMICE-030` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** DROPPED 2026-09-24 — Sean's call. It was already recorded as BY
DESIGN ("many features need flop stages") and deferred far; dropping it says
so in the tracker's own vocabulary rather than leaving an issue open that
nobody intends to resolve. The measurements stay valid history -- they are why
the close-page residual in [[ISSUE-002]] was accepted on the same grounds.
(was: DEFERRED FAR 2026-09-22, P3)

**Sean 2026-09-22: "030 is this way by design, many features need flop stages,
so defer 030 far into the future."** The latency is the price of the pipeline
those features live in, and it is accepted. Do NOT re-raise it as "the largest
identified defect left", do NOT re-measure it to make the case again, and do
NOT trade pipeline depth for it without being asked. The measurements below
stay because they are correct and because they size what the choice costs --
they are documentation of a trade, not an open bug.

The consequence worth REMEMBERING rather than fixing: small-burst read
bandwidth is `outstanding / latency` and nothing else, so the lever that is
still legitimately available is the OUTSTANDING dial (ceiling 32, and the
board proves it -- AxLEN 2 and 4 both reach ~94.5% at 32 outstanding where
they sit at 35%/68% at 8). Reach for that, not for the pipeline.

(Historical framing below, from when this was believed to be a defect.)

**The bug: ~49 MC cycles of read latency against LiteDRAM's 24.7** on the same
board, the same PHY and the same harness. Roughly 24 cycles of extra pipeline
for the same DRAM access. Neither 2026-09-10 bandwidth fix (the intake admit
stage, the return-ring depth) moved it.

**Why it matters beyond latency: it caps small-burst read BANDWIDTH.** Reads at
AxLEN 1/2/4 reach 16%/31%/60% of peak while writes hold 95% on the same
addresses. This was previously written off as "per-transaction overhead, a
mechanism nobody has identified". It is identified: **Little's law**, against
the read generator's 8-outstanding-burst budget.

Model: `min(8 x AxLEN / (read_latency + AxLEN), 0.95) x 8 B x 75 MHz`

| AxLEN | predicted MB/s | measured 2026-09-10 | measured 2026-09-14 | rd latency |
|---|---|---|---|---|
| 1 | 90.7 | 96.2 | 98.3 | 51.9 |
| 2 | 192.0 | 188.1 | 196.3 | 48.0 |
| 4 | 351.8 | 359.9 | 368.2 | 50.6 |
| 8 | 570.0 | 570.5 | 570.5 | 50.2 |
| 16 | 570.0 | 570.7 | 570.8 | 96.0 |

Board-measured with `bin/axlen_sweep.py`. The 2026-09-14 column re-takes the
curve on the rewritten harness (bridges removed, 4+4 generators, new data
function) at the same 8 outstanding: the fit survives, so the model is not an
artifact of the old measurement path. `axlen_sweep.py` had to be repaired
first — it was missing `import sys` and had never been runnable since its
original commit f02a4b569.

**DIRECT confirmation, 2026-09-14: the outstanding sweep.** The table above is
still an inference from a bandwidth curve. `bin/outstanding_sweep.py` tests the
claim head-on — if the shortfall is Little's law, the knee must sit near
`latency/AxLEN` and must move as `1/AxLEN`:

| AxLEN | model knee | measured knee | ratio |
|---|---|---|---|
| 1 | 47.7 | none inside 32 (390.6 MB/s at 32, still climbing) | — |
| 2 | 24.1 | 24 | 0.99x |
| 4 | 12.7 | 12 | 0.95x |
| 8 | 6.9 | 8 | 1.17x |

Every model knee at AxLEN 1 and 2 sits at or above the harness's own 32-deep
ceiling, which is why this could not be measured before the runtime dial
existed. The bandwidth values themselves fit the model to 0-6.5%.

**The model is exact, and an earlier version of this task said otherwise.** On
2026-09-14 this table reported the knees at 32 / 24 / 12 and called the 1.3-2x
gap to the model an open anomaly. That was a defect in the SWEEP's knee
detector, not in the controller: it fired on "this point did not gain 3% over
the previous one", which names the first point AFTER saturation, one sweep step
late every time. Scored as "the first N that reaches 95% of the plateau" the
knees land at 0.99x, 0.95x and 1.17x, and the 1.17x is only the sweep grid —
the model wants 6.9 and the available steps are 4 and 8. Fixed in
`bin/outstanding_sweep.py` and re-measured on the board; both the 1/AxLEN
scaling and the constant hold.

The per-point fit is just as good. At AxLEN 4 the model tracks every one of the
eight points from -0.1% to +4.4%, and measured bandwidth sits slightly ABOVE
the prediction throughout, which says the effective latency is marginally
better than the sampled average rather than worse.

**The decisive result: the shortfall RECOVERS COMPLETELY when the budget is
raised.** This is the claim's strongest test — if small-burst reads were losing
bandwidth to per-transaction overhead, more outstanding transactions would not
buy it back. They do:

| AxLEN | at 8 outstanding | best reached | at |
|---|---|---|---|
| 1 | 98.7 MB/s (16.4%) | 390.6 MB/s (65.1%) | 32, still climbing |
| 2 | 196.6 MB/s (32.8%) | **573.1 MB/s (95.5%)** | 24 |
| 4 | 367.9 MB/s (61.3%) | **574.6 MB/s (95.8%)** | 16 |
| 8 | 575.0 MB/s (95.8%) | 575.6 MB/s (95.9%) | 12 |

AxLEN 2 and 4 reach the SAME ~95.8% ceiling as AxLEN 8 once enough reads are in
flight. There is no per-transaction penalty left to explain. AxLEN 1 needs ~49
in flight and the harness ceiling is 32, which is why it alone is still
climbing — not a different mechanism, just a budget that has not reached its
knee.

This also sharpens the fix. The latency is still the defect for a real master
with a shallow budget, but it is now measured that the CONTROLLER can be driven
to 95% at AxLEN 2 — so nothing in pumice's datapath is limiting small bursts.

Durable records: `reports/axlen_sweep.json`, `reports/outstanding_sweep.json`.
Both sweeps only printed until 2026-09-14, which is why the tables above were
previously quoted from scrollback with no artifact to re-derive them from.

**Two things this rules out.** It is NOT a scheduling bug, and specifically it
is NOT "the read cannot be scheduled until the write is consumed on AXI" (a
reasonable guess, checked and discarded): the characterization runs a write
phase to completion and THEN a read phase, so no writes are in flight while the
reads are measured. (That sequencing is also why PUMICE-037 went unseen for so
long: nothing in this area ran both directions at once with a gap until the
2026-09-14 bank/gap sweep.) It is also not the return ring -- the shortfall did not move
between depth 32 and 64.

**Why writes are immune.** pumice returns B at CAM commit, not after a DRAM
round trip, so a write burst retires in a fraction of a read's time and the same
8-burst budget is ample.

**The fix is the latency, and it closes the bandwidth gap with it.** At
LiteDRAM's 24.7 cycles the same 8-burst budget covers AxLEN 4 (8x4/28.7 = 1.11,
i.e. no longer binding) and the shortfall vanishes from AxLEN 4 upward.
Raising `GEN_MAX_OUTSTANDING` in the harness would ALSO move the numbers, but
that is moving the measurement, not fixing the controller -- a real master with
few outstanding reads would still see the latency.

**Where to look.** The read path crosses intake -> rd CAM -> arbiter -> DFI ->
PHY -> aligner -> return ring -> R channel. `ch01_overview/04_pipeline_latency.md`
in the MAS has the per-stage flop counts from the elaborated netlist; compare
that budget against the measured 49 and find the stages LiteDRAM does not have.
The AR-order return ring and the reorder CAM are the obvious suspects, and both
are research features -- this may be a deliberate cost rather than a defect,
but nobody has done the accounting to say which.

---


## 2026-09-24 — DROPPED

Dropped rather than closed: nothing was resolved, the design simply carries
this cost deliberately. The convention reserves `dropped` for "ended without
completing (abandoned / superseded / won't do)", and "won't do" is exactly the
standing position -- shortening the ACT->column path means removing pick-
pipeline or bank-timer flop stages, which Sean ruled out of scope.

Kept for reference because two other items lean on it: the [[ISSUE-002]]
close-page residual was accepted on this ruling, and the outstanding-dial
measurements here (static_close flat at 33.9 MB/s across OS 8/16/32) are what
showed the residual is not latency- or outstanding-bound.
