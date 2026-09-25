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


## 2026-09-24 (later) — CORRECTION: I misread the watermark, twice

Sean, on my explanation: *"If it only ever lets one write batch then it stops,
that is broken. For write heavy traffic, 8 or 16 might make sense."* The
premise he was reacting to was mine and it was wrong.

**`wr_low_wm` is a FLOOR the drain runs down to, not a gap.** `w_wr_occ` is the
popcount of `wr_sch_valid_i` over `NUM_ENTRIES = 8` -- the write CAM -- and the
drain clears on `w_wr_occ <= sched_wr_low_wm_i`. So:

| watermarks | arms when | drains to | batch length |
|---|---|---|---|
| hi=2 / lo=1 (shipped) | 2 pending | 1 left | **up to 7** |
| hi=8 / lo=4 | CAM FULL (8) | 4 left | 4, and needs a full CAM to start |

The shipped setting gives LONGER batches that arm MORE readily. That is why it
measured best (314.0 vs 284.1 MB/s, against a 600 MB/s ceiling) -- a result I
had recorded as surprising and "overturning my hypothesis" when it is simply
what the mechanism does. Batching is working, and working well.

**The real reason `wr_batch_max=16` never binds is structural: the write CAM is
8 deep, so a batch can never exceed `8 - low_wm = 7`.** The default cap sits
above the hardware maximum. Not "the watermark gap is 1" -- that framing was an
artefact of reading `low_wm` as the far end of a window.

**So the defect is narrower than both of my earlier write-ups.** The cap is
dead surface because it is set above what the hardware can produce, on a build
where the CAM is 8. It is not evidence that batching is inert, and the
watermarks should NOT be widened -- that measurably costs bandwidth.

Sensible resolutions, in order of cost:
1. Default `wr_batch_max` to something inside the reachable range (<= 7) so the
   knob does something, or
2. Derive its clamp from NUM_ENTRIES the way `POSTPONE_MAX` is derived from
   MAX_PENDING (`refresh_ctrl.sv`), so it cannot be programmed above the
   structural maximum and a host write that would be inert is visibly clamped
   on readback, or
3. Document it as a bound for deeper-CAM configurations and leave it.

(2) is the one that matches how this codebase already handles exactly this
problem one module over, and it makes the inertness impossible rather than
merely documented.


## 2026-09-24 (third pass) — max is NOT redundant, and there is no defect here

Sean: *"If there are hi/lo values already, what is the point of max? It seems
redundant and confusing."* Re-read the FSM. It is not redundant, and my
previous two write-ups were both wrong in the same direction.

**`r_wr_batch_cnt` counts WRITES ISSUED, not occupancy.** That is the detail
both earlier passes missed. The two bounds therefore cover different writers:

| writer | what ends the drain |
|---|---|
| bursty (CAM drains faster than it refills) | `occ <= low_wm` -- writes ran out, reads get slots naturally |
| continuous (refills as fast as the drain empties) | occupancy NEVER reaches low_wm, so **only the cap can end it** |

The second row is the entire justification. Against a saturating writer the
watermarks are structurally incapable of ending a drain, which is precisely the
read starvation fixed in `fc83c1b3c`. The RTL says so: *"0 = unbounded = the
original starvation."*

And the two exits are not equivalent even when both could fire. The CAP exit
sets `r_rd_owed = 1`, blocking re-arm until a read actually fires; the
OCCUPANCY exit does not. So the cap is a GUARANTEE ("a read goes before writes
win again") where the watermark is only an OPPORTUNITY that a refilling writer
closes on the next cycle.

**hi/lo tune throughput; max bounds starvation.** Different jobs, both needed.

**Retracting both earlier claims:**

- "the drain runs about one write" -- wrong, `low_wm` is a floor, not a gap.
- "a batch can never exceed `8 - low_wm = 7`, so 16 is above the structural
  maximum" -- wrong, that conflates CAM occupancy with issue count. Under a
  saturating writer the batch length is unbounded by occupancy and 16 is
  reachable and meaningful.

**So the "unreachable knob" framing is withdrawn entirely, and with it the
proposed NUM_ENTRIES-derived clamp -- which would have been an actively harmful
fix**, capping the one bound that protects against starvation at a value
derived from a structure it has nothing to do with.

What my measurement actually showed: `wr_batch_max` 0 vs 16 were
indistinguishable *because the test workload's writer ran dry each drain*, so
the occupancy exit fired first and the cap was never consulted. That is a
property of the STIMULUS, not of the knob -- and it is the same trap as the
original PUMICE-047 mutation, which "passed" for the same reason.

**What is actually left of this task:** part A, a test that exercises the cap,
and it now has a clear shape -- a SATURATING writer (one that refills faster
than the drain empties, so occupancy stays above `low_wm`), then vary
`wr_batch_max` and show the batch length follows it. That is the only
configuration in which the knob is observable, and no existing profile produces
it.


## 2026-09-24 (fourth pass) — part A ATTEMPTED AND NOT LANDED

I tried to write the saturating-writer test and did not get it to a state worth
committing. Nothing was shipped; the arbiter suite is green and unchanged.
Recording what was learned so the next attempt starts ahead of this one.

**Evidence the knob WORKS, captured directly.** Instrumenting the drain FSM in
the fub TB (all 8 write slots schedulable so occupancy pins at NUM_ENTRIES,
`wr_low_wm = 0` so the occupancy exit can never fire, `wr_batch_max = 1`):

```
drain=1 owed=0 cnt=0 rdcol=1 wrcol=1 occ=8   <- cap fires here
drain=0 owed=1 cnt=0 rdcol=1 wrcol=1 occ=8   <- drain cleared, read debt set
```

The cap arms the drain, allows one write column, clears the drain and records
`r_rd_owed`. That is the mechanism doing exactly what it is for, observed on
the registers rather than inferred from bandwidth. An assertion on that single
batch (`fires == 1` and `capped`) PASSES.

**Two testbench limits blocked a complete test**, and both come from the same
property that makes the writer saturate -- entries never retire:

1. **The read side exhausts.** A read column is marked in-flight when it is
   SELECTED (`w_rd_col_inflight_ent`, ~line 384), not when it retires, so after
   a few picks `rd_col_f` sits at 0 and no read ever fires. `r_rd_owed` is
   therefore never paid, the drain cannot re-arm, and a SECOND batch is
   unobservable. Asserting across batches would be testing the entry model.
2. **`wr_batch_max = 0` did not behave as the control.** The drain armed on 0
   of 40 cycles where `= 1` armed, which cannot be right -- the cap does not
   gate arming, only clearing. That is an unexplained discrepancy in MY
   stimulus or sampling, not a demonstrated DUT property, and it is exactly the
   control the test needs to show the knob is what bounded the batch.

**Do not treat the single-batch pass as sufficient.** Without a working
`wr_batch_max = 0` control it does not exclude something else clearing the
drain after one write.

**For the next attempt.** The fub TB's never-retiring entry model is the wrong
vehicle: it is what creates the saturating writer AND what starves the reader,
and those two needs conflict. Either extend the TB to retire entries (a real
change, affecting other tests) or move the test up to the CORE level, where
real CAMs retire and a genuinely saturating writer can be driven through the
BFMs while reads continue to complete. The core level is probably right --
it is also where the behaviour matters.

**Caveat on everything above:** I have now misread this drain FSM three times
in one session (the "one write" reading, the "CAM depth caps it at 7" reading,
and the "max is redundant" framing). Each was corrected only after Sean pushed
back. Treat my descriptions of this block as provisional until a test exercises
the path.
