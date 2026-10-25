# TASK-021: stream-g one-channel 16-descriptor chain is slowest at 32 beats a descriptor

**Priority:** P3
**Status:** open -- filed 2026-10-24 from the stream-g board profiles (TASK-020 phase 6)
**Owner:** sean galloway

## What was measured

`gscale1` on the Genesys 2 (`build-perf/results/gscale1_2026-10-24_{fsm,g}.json`, channel 0 alone, a
16-descriptor chain per point, 16 bytes a beat, 100 MHz), cycles from the kick to the last write:

| beats per descriptor | STREAM | stream-g | STREAM / stream-g |
|---:|---:|---:|---:|
| 8 | 233 | 671 | 0.35 |
| 16 | 310 | 824 | 0.38 |
| 32 | 559 | 1,897 | 0.29 |
| 64 | 1,071 | 1,737 | 0.62 |
| 128 | 2,095 | 2,409 | 0.87 |

STREAM is monotonic; stream-g takes longer at 32 beats than at 64, and the 32-beat point is the only
one in the one-channel chain column that moves against the trend (the 8-channel chain column is
monotonic: 0.91 at 16, 0.98 at 32, 1.00 at 64). The point measured the same on both runs of the day
(gcompare has no b32 point; gscale1 ran once per design). With every channel busy the point does not
stand out, so whatever it is lives in the lone-channel interplay of the firmware's STAGE timing and
the read-ahead prefetch's in-place advance (MAS 7.2): the likely shape is that at 32 beats the chained
head is staged just after the write side's advance window closes, so each descriptor walks
COMPLETE / NEXT_DESC instead of advancing in place, and the walk's full per-descriptor firmware cost
(about 70 cycles here) is paid 16 times.

## The simulation's view (2026-10-24, `gscale1-g-2of2`)

The harness sim of the same bitstream design gives 1,768 cycles at 32 beats and 1,927 at 64 (board: 1,897 and
1,737), while STREAM's sim matches its board to the cycle on every point. So the knee is not a fixed cost: it
moves with the phase of the kick against the firmware's poll loop, which differs between the sim's UART timing
and the board's. Step 1 below should therefore sweep the kick phase (or the firmware's poll start) at 32 and
64 beats, not just read one waveform.

## What to do

1. Reproduce in the harness sim (`make sim-gscale1`, cell `gscale1-g-2of2`; the sim matches the board
   cycle for cycle) and look at `scheduler_g` on channel 0: count in-place advances (`wr_advance`)
   against COMPLETE / NEXT_DESC walks per descriptor at 16, 32 and 64 beats.
2. If the walk is the cause, decide whether the firmware's poll order or the STAGE timing can be
   brought inside the advance window at that size without costing the other points (the 8-channel
   column is already at parity there), or document the knee.
3. Record the outcome in STREAM HAS 5.4 (Table 5.4.5's one-channel chain column) and MAS 7.4.

## Related

- stream TASK-020 (stream-g), HAS 5.4, MAS 7.2 / 7.4
