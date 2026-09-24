# TASK-008: no test bounds the write drain, and the cap is unreachable at the shipped watermarks
> **Was `PUMICE-049` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** open 2026-09-24  **Priority:** P3 — coverage gap plus a usability
finding; nothing is broken, the knob just cannot act where it ships

Residue of [[ISSUE-003]], which disproved the clobber. Two parts.

**A. `wr_batch_max` has no test that bounds the drain.** The arbiter fub TB
pins `sched_wr_high_wm_i = 0` (batching off), so the whole batching path --
drain, cap, `r_rd_owed` hysteresis -- is uncovered at fub level. The top-level
gen_replica cells exercise it but cannot ASSERT the bound, only the outcome.

A first attempt at a fub test is instructive and is why this is filed rather
than fixed: holding all 8 write slots schedulable with `low_wm=0` (so the
occupancy exit can never fire) produced 40 consecutive write columns at
`batch_max=1` -- which looks like the cap failing, but instrumenting
`r_wr_drain` showed it armed on only 1 of 40 cycles. Writes were winning for
an unrelated reason and the cap was never engaged, so the assertion was firing
on a premise the stimulus had not established. A valid test must PROVE the
drain is armed before it can claim anything about the bound.

**B. The cap is unreachable at the shipped watermarks.** `w_batch_done` is one
of three drain exits, and `w_wr_occ <= sched_wr_low_wm_i` is independent of it.
At hi=8/lo=4 the drain ends after ~4 writes, so the default cap of 16 never
binds: `wr_batch_max` only acts when it is below `(wr_high_wm - wr_low_wm)`.
Measured: at hi=8/lo=4, batch_max 16 and 0 are indistinguishable; at hi=8/lo=0
they separate (11.5 s vs 17.6 s).

So either the default cap should be below the default watermark gap, or the
field should be documented as a narrow-window knob. Worth settling alongside
[[ISSUE-004]], which re-measures the batching gain.


## 2026-09-24 — part B answered, and the premise behind it was wrong

**Shipped defaults (pumice_csr.rdl): `wr_high_wm=2`, `wr_low_wm=1`,
`wr_batch_max=16`.** The watermark gap is 1, so the occupancy exit
(`w_wr_occ <= wr_low_wm`) ends a drain after about one write column and a cap
of 16 can never bind. The cap IS dead configuration at the defaults -- that
part of the filing is confirmed.

**But the conclusion I drew from it was wrong.** I reasoned that a batch of ~1
write amortises no turnaround, so batching must be nearly inert as shipped.
Measured on the board (`seq_wr_batch`, 1 writer + 1 reader, open_page, bus
MB/s, 0/2 failing everywhere):

| watermarks | gap 12 | gap 15 | vs disabled |
|---|---|---|---|
| hi=0 (disabled) | 240.7 | 209.3 | -- |
| **hi=2 / lo=1 (shipped)** | **314.0** | **263.0** | **+30.5% / +25.7%** |
| hi=8 / lo=4 | 284.1 | 254.8 | +18.1% / +21.7% |

The shipped defaults are not inert, they are the BEST of the three, and they
beat the wider window. With a tight watermark the drain re-arms constantly, so
writes stay clustered while reads never wait long; the wider window buys more
amortisation per drain and pays for it in read latency, and the combined bus
number is worse. A "batch of one" still groups writes relative to strict
alternation, which is where the gain comes from.

**So: do not lower the cap to make it bind, and do not widen the watermarks to
give it room.** Both would trade measured bandwidth for a knob that is doing
nothing wrong by being unreachable. `wr_batch_max` is a SAFETY BOUND for
wide-watermark configurations -- the thing that stops an unbounded drain
starving reads, which is what it was added for -- not a day-one tuning knob.
The right change is documentation, not defaults.

**Part A (a test that bounds the drain) is still open, and is now low value.**
It would have to force a wide-watermark config where the cap can bind, i.e. a
configuration the measurements above say not to ship. A first attempt is
recorded above; note additionally that the arbiter fub TB gives no visibility
into `r_wr_drain` through its normal helpers, so the test needs the internal
signal or a new strobe.

**Also settles [[ISSUE-004]]:** the +25-30% batching gain in the record is
REPRODUCED on the fixed drain (+25.7% to +30.5%). It was not an artefact of the
broken drain.
