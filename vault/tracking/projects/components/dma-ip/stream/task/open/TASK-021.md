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


## The probe (board, stream-g, 2026-10-24 17:49; `build-perf/csv/task021_probe.csv`, `results/task021_probe_2026-10-24_g.json`)

A finer grid around the knee, each a 16-descriptor chain on channel 0 alone. `r2r` is the harness timer's
first-read to last-read span, so it excludes the kick-to-first-read phase; "per desc" is r2r / 16:

| beats | cycles | r2r | per desc | beats of data per desc |
|--:|--:|--:|--:|--:|
| 16 | 684 | 599 | 37 | 16 |
| 20 | 1,474 | 1,259 | 79 | 20 |
| 24 | 1,466 | 1,263 | 79 | 24 |
| 28 | 1,463 | 1,267 | 79 | 28 |
| 32 | 1,890 | 1,687 | 105 | 32 |
| 36 | 1,878 | 1,691 | 106 | 36 |
| 40 | 1,875 | 1,695 | 106 | 40 |
| 44 | 1,879 | 1,699 | 106 | 44 |
| 48 | 1,893 | 1,703 | 106 | 48 |
| 56 | 1,890 | 1,711 | 107 | 56 |
| 64 | 1,911 | 1,719 | 107 | 64 |
| 80 | 1,743 | 1,663 | 104 | 80 |
| 96 | 2,336 | 2,143 | 134 | 96 |
| 128 | 2,392 | 2,207 | 138 | 128 |

Five repeats each: 32 beats r2r 1,687, 1,679, 1,687, 1,687, 1,687 (totals 1,753 to 1,896);
64 beats r2r 1,719, 1,719, 1,719, 1,719, 1,719 (totals 1,907 to 1,935).
Shorter chains at the same sizes:

| beats | descriptors | cycles | r2r | per desc |
|--:|--:|--:|--:|--:|
| 32 | 2 | 369 | 175 | 88 |
| 64 | 2 | 286 | 199 | 100 |
| 32 | 4 | 573 | 391 | 98 |
| 64 | 4 | 603 | 423 | 106 |
| 32 | 8 | 1,003 | 823 | 103 |
| 64 | 8 | 1,036 | 855 | 107 |

What it says:

- **The chain is paced by the firmware, in bands, not by the data.** From 32 to 80 beats every chained
  descriptor costs 104 to 107 cycles of read span whatever its length; from 20 to 28 beats, 79; at 16
  beats, 37; from 96 beats up the data sets the pace again (96 + 38, 128 + 10). The "knee at 32" of the
  first sweep is the step from the 79-cycle band into the 106-cycle band, and the 64-beat point sits in
  the same band, so the 1,737 of the first run (against 1,911 to 1,935 here) was a lucky phase, not a
  faster regime.
- **The read span repeats to the cycle; the total does not.** Identical points give identical r2r and
  totals 140 cycles apart, so the kick-to-first-read phase (where the firmware's poll loop stands when
  the kick lands) is the whole of the run-to-run spread, and the simulation's different numbers at 32
  and 64 beats (1,768 / 1,927) are that phase, not a different design.
- **Shorter chains pay the same per descriptor** (two to eight descriptors: 88 to 107 per descriptor at
  32 and 64 beats), so the cost is per head, not an end effect.

The bands are multiples of about 27 cycles, which is the shape of a hart's poll loop over its slots.
The mechanism to confirm in the waveform (step 1 below) is therefore: a chained head becomes visible
(HEAD valid after the descriptor engine's fetch), the hart sees it one poll pass later and STAGEs it, and
whether the read side can still advance in place depends on whether that STAGE lands before the running
descriptor's last read; below the band edge it does not, the channel walks COMPLETE / NEXT_DESC, and the
next head's fetch does not start until the walk, which puts the next STAGE a whole band later. The fix,
if one is wanted, is on the firmware side (stage the chained head earlier in the pass, or let the hardware
pre-stage a chained legacy head the way the FSM takes it) and it is worth about 16 x 70 cycles on a
lone channel's short chain and nothing with every channel busy.


## The mechanism, from the simulation trace (2026-10-24, board geometry, `results/task021_trace_2026-10-24_g.jsonl`)

With the simulation in the board's configuration (USE_AXI_MONITORS=0; the first sim pass had the package's
monitors built in) the sim is the board: 688 / 1,900 / 1,739 / 2,410 cycles at 16 / 32 / 64 / 128 beats against
the board's 684 / 1,890 / 1,737 / 2,409. Channel 0's scheduler was sampled every clock through the four points
(`bin/sched_trace_timeline.py`):

| beats | per-descriptor pattern | cycles between starts | head valid -> STAGE | idle after the last read on a walk |
|--:|---|--:|--:|--:|
| 16 | take, then 14 in-place advances | 32, 32, 32 ... | (head staged before the previous start) | -- |
| 32 | walk, advance, walk, advance ... | 167 + 49 = 216 a pair | 1 (walk), 10 (advance) | 175 |
| 64 | walk, advance (+ one double advance) | 135 + 81 = 216 a pair | 26-50 | 160-168 |
| 128 | walk, advance, advance | 143 + 145 + 128 | 90-106 | 104 |

So:

1. **The in-place advance happens only for a head the firmware has STAGEd before the running descriptor's last
   read** (`head_ok = r_staged`, MAS 7.2). At 16 beats the heads are staged ahead and the chain runs on the
   firmware's STAGE cadence, 32 cycles a descriptor (twice the data), all advances.
2. **From 32 beats the STAGE lands after the last read for every second descriptor.** That descriptor walks
   COMPLETE -> NEXT_DESC: the channel drains its writes, the firmware notices COMPLETE / the head in NEXT_DESC
   on a later pass and stages it, and the take comes 135-175 cycles after the last read with no read issued.
   The one after it advances in place (its head was fetched during the walk and staged in time). The pair costs
   216 cycles at 32 and at 64 beats alike: the 106-cycle-per-descriptor plateau of the board probe.
3. **The firmware's reaction to a new head is 26 to 106 cycles** (one poll pass of a hart over its slots, with
   the barrel issuing each hart every fourth cycle), which is why a 64-beat read window (about 81 cycles between
   advances) still misses half the time, and why the run-to-run spread is one walk (about 170 cycles): whether
   the chain starts on an advance or a walk depends on where the hart's pass stands when the kick lands
   (board 1,737 against 1,911-1,935 at 64 beats; the sim's 1,739 is the former phase).
4. Above about 96 beats the read window exceeds the reaction time and the chain is data-bound again.

Options, for the owner (none taken; the measurement stands): (a) firmware -- stage a chained head the moment it
appears, ahead of the pass's other work (cheap, bounded by the pass length); (b) hardware -- let `scheduler_g`
treat a chained legacy head as staged for the in-place advance when the firmware has staged the running
descriptor with ARM_NEXT, the FSM's own behaviour, keeping the firmware's validation for EXT and over-ALG_MAX
heads; (c) leave it: with every channel busy the other channels' data hides the walk (Table 5.5's 8-channel
chain column is at parity from 64 beats) and a lone channel's short chain is the only case that pays.


## Root cause (2026-10-24, the trace read against the firmware)

The windows are identical in rapids-g and stream-g (`seq_attn`, `w_head_open`, HEAD_SUM), and so is the image.
In the trace, a head that opens on a TAKE is staged 39 cycles later (the next pass's first HEAD_SUM read sees
13 and takes the chain hook); a head that opens on an in-place ADVANCE is staged 165 cycles later, although
`desc_head_valid` never dropped and the head was open from the cycle after the advance. The firmware's one-slot
loop (`sched_g.S`, `one_loop`) explains the difference: the chain hook (`HEAD_SUM == 13 -> one_chain`) is
tested only on the pass's FIRST HEAD_SUM read; when that read finds the previous head still staged, the loop
reads SUMMARY, and a head that opened in between is read again and sent to `one_judge` (the full JUDGE path,
about 150 cycles at 8 clocks an instruction) -- "a head that came after the first read is judged here". In
rapids-g a chained head opens at the take the firmware's own STAGE caused, so the next pass's first read sees
it and the hook fires; in stream-g it opens at the hardware's advance, which lands anywhere in the pass, and
about half the time it lands after the first read.

So: rapids avoids it by construction (no in-place advance), not by a different mechanism; stream-g's extra
fast path exposes the loop's asymmetry. The fix is two instructions in `one_loop` (test the second HEAD_SUM
read for 13 and take `one_chain` there too; the two-slot and slot loops already read HEAD_SUM after SUMMARY and
hook on it), in the SHARED image: it needs `gen_rapids_g_fw.py`, both equivalence benches and the stream-g
board run again, and it would move rapids-g's own numbers only where a head opens late in a pass (its lone-
channel short chains). Owner's call, since rapids is closed.

## What to do

1. Done above: the trace counts advances against walks at 16, 32, 64 and 128 beats.
2. If the walk is the cause, decide whether the firmware's poll order or the STAGE timing can be
   brought inside the advance window at that size without costing the other points (the 8-channel
   column is already at parity there), or document the knee.
3. Record the outcome in STREAM HAS 5.4 (Table 5.4.5's one-channel chain column) and MAS 7.4.

## Related

- stream TASK-020 (stream-g), HAS 5.4, MAS 7.2 / 7.4
