# TASK-005: the paging predictors are built unconditionally and the board never uses them
> **Was `PUMICE-034` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** CLOSED 2026-09-24 — **option 3: leave them.** Sean's call, and it
corrects the recommendation this task had been carrying. (was: open 2026-09-14,
P2 — pure headroom, no correctness impact)

`u_page_policy` (the mode 5 row predictor plus the mode 6/7 RBL table) is
**4,546 LUT / 3,341 FF**, a third of pumice's LUTs, instantiated with no build
gate. The board's default runs use `open_page` and never select modes 5/6/7, so
that area is carried and never exercised on a part where it is the difference
between comfortable and tight.

It is also where timing dies first when anything else grows: across the
2026-09-13 builds `u_row_pred` owned 340-920 of the failing endpoints every
time, more than any other block.

**The tension, which is why this is not simply a fix.** The modes were restored
specifically so that ONE bitstream characterizes every policy
([[project_pumice_advanced_sched_modes]]). Gating them trades that away for
area. Both positions are defensible and it is Sean's call, not a session's.

**Options, in increasing order of how much they give up:**
1. A `PAGE_PRED_MODES` parameter defaulting ON, with the board build turning it
   off. One bitstream per policy family instead of one for all.
2. Gate only the RBL table (248 LUT / 1,488 FF) and keep the row predictor.
3. Leave it and accept the area; revisit if a build stops closing.

**Context for the decision:** the four-generator build closes at **+0.016 ns**
with **87.1% slice occupancy**. There is not much room left for anything else to
grow, and this is the largest single block that is optional.

---


## 2026-09-24 — re-measured, and TASK-002 supplied the missing half

**The block is BIGGER than filed.** Re-measured by OOC synth on
xc7a100tcsg324-1 (NUM_BANKS=8, ROW_WIDTH=13):

| | filed 2026-09-14 | measured 2026-09-24 | change |
|---|---|---|---|
| `pumice_page_policy` | 4,546 LUT / 3,341 FF | **5,578 LUT / 3,342 FF** | **+1,032 LUT** |

8.8% of the device in one optional block, on a part whose four-generator build
closes at +0.016 ns and 87.1% occupancy.

**And now we know what it buys, which the filing could not say.** The TASK-002
board campaign measured every predictor against plain open page (75 MHz,
8000 txn, read MB/s):

| mode | incremental | col_major | vs plain open page |
|---|---|---|---|
| plain `open_page` | 554.1 | 163.8 | -- |
| 4 `adapt_time` | 554.1 | 163.8 | **identical** |
| 5 `adapt_access` | 554.1 | 163.8 | **identical** |
| 7 `rbl_dyn` | 549.7 | 163.8 | -0.8%, +33 ACT |
| 6 `rbl_static` | 554.1 | 163.8 | identical *(after the epoch fix; 34.9 before)* |

**Not one of modes 4/5/6/7 beats plain open page on any workload measured.**
Two are bit-identical, one is marginally worse, and the fourth was a 15.8x
regression until [[TASK-001]]'s P1 was fixed. So the block currently costs
5,578 LUT and returns nothing measurable.

**That is not yet a decision, and here is the honest counterweight.** The
campaign swept ONE AXIS AT A TIME against a fixed baseline. The predictors are
exactly the kind of mechanism that earns its keep on a workload that ALTERNATES
locality -- which is what the axis PAIRS and a genuinely random family would
probe, and neither has been run (see TASK-002, "What is NOT yet characterized").
Gating the block now would make that experiment require a different bitstream,
which is the property the modes were restored to avoid
([[project_pumice_advanced_sched_modes]]).

**Recommendation, for Sean's call:** option 1 (a `PAGE_PRED_MODES` parameter
defaulting ON, board build OFF) but NOT YET -- finish TASK-002's pair sweep
first, because it is the only experiment that could still justify the area, and
it is cheap now that the telemetry reads. If the pairs also show no benefit,
the block has no measured defence and option 1 becomes straightforward. If a
build stops closing before then, take option 1 immediately; the numbers above
are the justification.


## 2026-09-24 — the pair sweep ran; it removes the last defence

The recommendation above was "option 1, but not yet -- finish the pair sweep
first, because it is the only experiment that could still justify the area".
It ran ([[TASK-002]], `pairs_paging_mix`, concurrent 1w+1r, three reps).

**It did not justify the area. It argued against it.** Under alternating
locality the predictors are identical to plain open page on 3 of 4 scenarios,
and `rbl_static` is a **-43% regression** on the fourth (98.3 -> 55.8 MB/s,
hit 81.3% -> 44.0%, ACT/txn 3.00 -> 8.96), reproducible to +-0.3 MB/s across
three independent runs. The predictor auto-precharges rows the other direction
was about to reuse -- wrong in precisely the situation it exists for.

So the position is now: **5,578 LUT (8.8% of the device) that is inert at best
and a 43% regression at worst, on a build closing at +0.016 ns.** There is no
measured workload on which any of modes 4/5/6/7 beats plain open page.

**Recommendation is unchanged in shape and now unblocked: option 1.** A
`PAGE_PRED_MODES` parameter defaulting ON, board build OFF. The one-bitstream
property it trades away was worth protecting while the predictors might have
earned their keep; they did not.

Still Sean's call -- the counter-argument is that a future workload class might
differ, and gating makes testing that need a rebuild. But that is now a bet
against three measured families plus the mix, rather than an open question.


## 2026-09-24 — CLOSED as option 3 (leave them), and why the recommendation was wrong

Sean: *"We have all of the modes to use them to see the effects."*

That is the answer, and it exposes a mistake in the reasoning above. I had
escalated from "option 1 but not yet" to "option 1, now unblocked" on the
strength of the pair sweep showing rbl_static at -43%. But **that result IS the
modes doing their job.** "rbl_static is harmful under concurrent traffic" is a
characterization finding, produced by having every mode reachable in one
bitstream. Gating them to save area would trade away the instrument that
produced the finding, in order to bank LUTs on a build that currently closes.

I was weighting 5,578 LUT above the thing the block exists for. The area is
only worth spending when a build actually stops closing -- which is exactly what
option 3 says, and what this task said from the day it was filed ("Both
positions are defensible and it is Sean's call").

**Standing: leave `u_page_policy` ungated. Revisit only if a build fails to
close**, at which point the measurements here (5,578 LUT / 3,342 FF, 8.8% of
the device, no mode beating plain open page on any measured workload) are the
justification and option 1 is the move.

What the measurements are still good for, and why they were not wasted: they
say the predictors cost area and return nothing *on the workloads measured so
far*, which is the input to [[TASK-002]]'s continuing characterization -- not a
reason to remove the modes. Follow-up on whether any generator can show
rbl_static a WIN is [[TASK-010]].
