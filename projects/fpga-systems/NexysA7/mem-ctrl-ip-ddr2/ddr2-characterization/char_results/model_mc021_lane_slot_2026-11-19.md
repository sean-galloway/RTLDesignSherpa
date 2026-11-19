# The lane is timed at its slot: the model's bank_interleave residual (memory-controllers MC-021 step 3, 2026-11-19)

**Question (MC-021 "What next" item 1):** after BUG-004 the SKU model sat at 53
in / 4 out against the board; the four out were the `bank_interleave`
`col_major` cells, read / write asymmetric on the board (bl4 258 / 351) and
symmetric in the model (333 / 333), with the model 14 percent UNDER the board
on bl8 (333 against 387) where every other close-page cell was over. The item
said: probe the read path after a read AP and the write fill on the proxy
before anything is tuned.

**Answer:** neither. The proxy reproduces the board on every one of the cells
(below), and the asymmetry is the DRAM's write-recovery hop over four banks.
The model's error was its own: it timed the DUAL_ISSUE lane's ACT in CK from
the odd tick it fires on, so a lane ACT followed by a main-slot ACT was spaced
5 CK where the RTL's MC-cycle counters space them 2 cycles (3 CK on the wire,
which the host's phase margin allows for). Under a close-page interleave every
third ACT paid the cycle: 2.4 slots per beat against the RTL's 2.0. Timing the
lane at its slot puts bl8 / bl16 on the board (389 against 387) and makes bl4
asymmetric the right way (283 / 389 against 258 / 351). Compare 53 / 4 ->
**55 / 2**; the SKU's 30 cells moved 0.6 percent at most. The two still out are
the bl4 read sides at +11 percent, a pick-pipeline fixed point named in
section 4 with its probe.

## 1. The proxy is the board on these cells

RTL sim, `test_granite_char_perf`, scheme 2 + close page, TEST_DUAL 1, pool 16,
100 MHz, 2048 transactions per pass (`scratchpad/mc021/dram_bi_bl{4,16}.json`,
`perf_bi_bl{4,16}.json`; bl8 from the BUG-004 run).

| cell | board wr / rd | proxy wr / rd | model 11-18 | model now |
|---|---|---|---|---|
| bank_interleave col_major_bl4 | 258 / 351 | 258.0 / 353.2 | 333 / 333 | 283 / 389 |
| bank_interleave col_major_bl8 | 387 / 387 | 386.5 / 386.1 | 333 / 333 | 389 / 389 |
| bank_interleave col_major_bl16 | 387 / 387 | 386.8 / 385.1 | 356 / 356 | 389 / 389 |
| bank_interleave col_major_interleaved_bl4 | 242 / 253 | -- | 246 / 279 | 246 / 281 |
| bank_interleave col_major_interleaved_bl16 | 387 / 387 | -- | 347 / 347 | 389 / 389 |

What the `col_major` family is under this preset: the generator strides by the
ROW_MAJOR geometry's row (16 KiB) while the map is `bank_lsb` 2, so the low
bits of every burst are zero and the AxLEN beats of one burst land on banks
0 .. AxLEN-1: four banks in play at bl4, all eight at bl8 and bl16. Every beat
is a miss (auto-precharge). The traces (MC cycles):

| | bl4 write | bl4 read | bl8 (either) | bl16 (either) |
|---|---|---|---|---|
| slots per beat | 3.10 | 2.28 | 2.07 | 2.07 |
| ACT -> ACT gaps | 2 (75 %), 6 (25 %) | 2 (81 %), 3 (19 %) | 2 | 2 |
| same-bank ACT period | 8 / 12 / 14 | 7 / 8 / 9 / 11 | 12-18 | 12-16 |
| AP -> ACT same bank | 6 / 7 / 9 / 10 (quarters) | 4 / 5 / 6 / 7 | 7-16 | 7-15 |
| ACT -> its column | 2 (50 %), 5 / 7 (25 % each) | 2 (73 %), 5 / 7 | 2 (67 %), 5 / 7 | 2, 5 / 7 |

Writes at bl4 are bound by the write auto-precharge hop: t_wr 4 + t_rp 2 = 6
cycles from the WRA before the bank's next ACT, over a four-bank rotation
whose ACTs then come 2, 2, 2, 6 apart (four ACTs per 12 cycles: 267 MB/s
ceiling, 258 measured). Reads pay t_rtp 1 + t_rp 2 and the pipeline, so the
four-bank rotation keeps the ACT stream at 2 with a 3-gap every fifth ACT.
With eight banks in play neither hop binds and both directions sit at the
tRRD ceiling (one ACT per 2 cycles: 400 MB/s, 387 measured) -- the ceiling
BUG-004 uncovered. Nothing in this is the read path or the write fill.

## 2. The model's error: the lane timed in CK

`granite_sku_controller.cpp` fires the lane's row command on the odd tick
(row_phase 1) and, until this step, checked its timing at that tick and
stamped the DRAM with it. The RTL's bank and rank timers are MC-cycle
counters that start at the fire's CYCLE whatever its DFI phase: a lane ACT in
cycle n and a main ACT in cycle n + 2 are t_rrd = 2 apart to `mc_global_timers`
(3 CK on the wire, 15 ns against the part's 10 ns tRRD -- the host's 5 ns
phase margin is exactly this case). The model's nRRD is the host's 2 MC cycles
in CK (4), so from an odd tick the next main-slot ACT was allowed 5 CK later,
not 4: every lane -> main ACT hop cost one CK, and the main -> lane hop another
(a main ACT at an even tick, the lane at the next odd tick past 4 CK = 5).
Under the close-page interleave the ACT stream is lane, lane, main (two of
three ACTs ride): 4 + 5 + 5 = 14 CK per three ACTs where the RTL spends 12,
which is the model's 2.4 slots per beat against 2.0 (bl8 debug window: 20,000
slots, 8,338 columns, 5,844 slots empty on a held ACT, 2,555 on a stale pick).

The fix (one rule, no knob): the lane's timing is checked at the slot tick and
the DRAM is stamped with the slot tick, so every hop from a lane command (tRRD
and tFAW to the next ACT, tRCD to its column, tRP after a PRE) is the RTL's
count of MC cycles, as the main slot's commands already were. Checked hop by
hop against the RTL's counters: ACT -> column from a lane ACT lands at cycle
n + 2 in both; ACT -> ACT same bank, ACT -> PRE and PRE -> ACT all round to the
same slot. The one place the stamp changes an outcome is the rank hop, which is
the error above. `tests/test_char_model.py` 36 / 36 and the vendor suites
217 / 217 after the rebuild.

Before / after on the three model configs, the board set `sku100bug004b_2026-11-18`
(`compare_model_sku_vs_board_sku100bug004b_lanestamp_2026-11-19.md`, 55 in / 2 out,
from 53 / 4). Every cell that moved:

| preset | cell | board | model 11-18 | model now |
|---|---|---|---|---|
| bank_interleave | col_major_bl4 | 258 / 351 | 333 / 333 | 283 / 389 (OUT, +9.7 / +10.9) |
| bank_interleave | col_major_bl8 | 387 / 387 | 333 / 333 | 389 / 389 (IN) |
| bank_interleave | col_major_bl16 | 387 / 387 | 356 / 356 | 389 / 389 |
| bank_interleave | col_major_interleaved_bl4 | 242 / 253 | 246 / 279 | 246 / 281 (OUT, +1.8 / +11.3) |
| bank_interleave | col_major_interleaved_bl8 | 387 / 387 | 371 / 371 | 389 / 389 |
| bank_interleave | col_major_interleaved_bl16 | 387 / 387 | 347 / 347 | 389 / 389 (IN) |
| bank_interleave | incremental_bl16 | 387 / 387 | 377 / 377 | 389 / 389 |
| close_page | col_major_interleaved_bl4 | 379 / 387 | 370 / 370 | 389 / 389 |
| close_page | col_major_interleaved_bl8 | 251 / 328 | 287 / 320 | 275 / 309 |
| close_page | col_major_interleaved_bl16 | 171 / 240 | 184 / 217 | 184 / 240 |
| close_page | mixed_bl8 (union) | 111 | 107 | 116 |
| close_page | row_thrash_bl8 | 246 / 251 | 250 / 275 | 249 / 271 |
| close_page | random_bl8 | 204 / 234 | 217 / 240 | 217 / 244 |
| defaults / open_page | col_major_interleaved_bl4 | 765 / 762 | 775 / 775 | 777 / 780 |
| defaults / open_page | mixed_bl8 (union) | 537 / 545 | 569 | 580 |

The SKU's open-page cells moved by the lane's share of their ACTs: +0.6
percent at most, `mixed_bl8` +2 percent (580 against the board's 537, +8.0,
tolerance 10). Everything else is unchanged.

## 3. Why the hop was invisible before BUG-004

With the global timers at N + 1 the lane never fired on a close-page chain
(BUG-004: 0 lane ACTs in 65,810), so the lane's timing never mattered there,
and on the open-page SKU the lane carries one ACT per row, under the error
bar. The fix uncovered the lane, and the lane uncovered its clock.

## 4. The residual: two bl4 read sides at +11 percent, a fixed point of the same rules

The pick probe (`PERF_PICK_PROBE`, bl4 read phase, cycles 116300-116363,
`scratchpad/mc021/pick_bl4_rd.json`) beside the model's slot debug
(`GRANITE_SKU_DEBUG`, `model_bi_bl4_dbg2.out`) shows both running the SAME
rules -- the hold (a winner whose bank opens within the pipe keeps the
register), the one-cycle hint, the stale pick after an auto-precharging
column, the lane riding beside a column only, rideable rows left to the lane
-- and settling into different periodic patterns on the four-bank rotation:

- RTL (12 cycles per four beats, read): an ACT whose bank opens while no
  column is firing cannot ride, takes the main winner register, and HOLDS
  there through the tRRD wait from the lane ACT before it (one cycle), then
  fires; the next ACT does the same. During the two holds the hinted columns
  lose their one-cycle hint (the hold has priority for the register) and
  fire later as plain requests: a quarter of the read columns at ACT + 5 /
  + 7. Probe cycles 116301-116305: `b2 ACT hold`, `b2 ACT fire`, `b3 ACT
  hold`, `b3 ACT fire`, then `b1 COL` at +5 and `b2 COL` at +7.
- model (12 slots per six beats): one held main-slot ACT per three lane
  ACTs; after each lane ACT the next slot is empty on a stale re-pick of the
  column that just fired (its request register still shows the old class
  for one slot, unmasked), and the hint lands in the freed register on
  time: every column at tRCD.

The term I first named here -- a registered read auto-precharge close the
model lacked -- was measured and is NOT it. Both probes (read phase
`pick_bl4_rd.json`, write phase `pick_bl4_wr.json`, 27 and 20 auto-precharges)
give the RTL's bank hops exactly as the model has them: column fire ->
`bank_act_ready` rise 5 for a read whose column fired at ACT + 2 (tRAS 5 from
the ACT, then tRP 2: the model's nRC = 7 MC from the ACT) and 3 for a late read
column (t_rtp 1 + t_rp 2: the model's RDA -> ACT 5 CK), 6 for every write (t_wr
4 + t_rp 2: the model's WRA -> ACT 11 CK); and the ACT request is visible one
cycle before the ready rises in both directions (39 of 39), which is the
model's request register with `pick_la` 2 (the decode sees the bank open within
two slots, the register is read the slot after). The fired column's stale
request stays visible one slot in both. A trial `ap_la` knob (the request one
slot later) put the write cells on the board (bl4 write 258.9 against 258,
interleaved bl4 272 / 242 against 253 / 242) and left the bl4 read at 389; it
was a knob matching a cell, not a term, and was removed before the commit.

What is left is the attractor itself. The RTL's read phase runs a steady
11-13-cycle pattern with one 3-gap from its first cycles (3-gaps at 114333,
114344, 114355, 114368 ... through the phase, no refresh involvement), the
model a steady 8-cycle one; the write phase likewise (RTL 12 cycles per four
beats with the 6-gap, model 11). The latency the RTL pays is measured: from
`bank_act_ready` rising to the ACT firing, reads 0 / 1 / 2 / 3 cycles in 5 /
13 / 7 / 2 of 27, writes 0 / 1 / 3 / 4 in 5 / 4 / 5 / 4 of 18, where the model
in its pattern pays 0 or 1. The next step that would settle it is a
cycle-aligned replay of the first 40 cycles of a phase in both (the proxy's
probe from the first ACT of the read phase beside the model's debug from its
first slot), to see which rule's timing sends the RTL into the pattern with
the double hold; until then the two cells stand at +11 with the mechanism
named and no term written for it.

## 5. What this says about the RTL

The RTL loses a quarter of its bl4 read columns to the held-ACT register --
the model, settling into the pattern without the double hold, is 11 percent
faster on exactly the two four-bank cells and identical everywhere else. That
is the price of MC-021 step 1's item 3 ("the winner that waits blocks the
ready column") where it binds: two cells of a close-page preset the SKU does
not ship, nothing on the SKU. It stays a question, not a change.
