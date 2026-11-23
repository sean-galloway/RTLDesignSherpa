# ISSUE-007: the bank_interleave per-pass levels are cadence modes the stream locks into after a refresh -- the proxy has them, the model does not

> memory-controllers ISSUE-007, 2026-11-23. The owner's "work on this". Steps 1 and 2
> of the issue's "what settles it": the SKU model's GO swept against its refresh
> phase, then the proxy (`test_granite_char_perf`, 100 MHz, `TEST_DUAL=1`, the
> phase-exact default, close page under `SCHEME_BANK_INTERLEAVE`, one generator)
> with the refresh interval moved a few cycles, its DRAM traces read by
> inter-refresh segment (`bin/dram_trace_segments.py`, new).

## 1. The board's levels are exact fractions

On the `bank_interleave` row-hit cells (`incremental_*`, `row_major_*` and
their multiid forms) the ten `every` runs since the phase-exact counters give
each direction one of three levels for the whole pass:

| level | MB/s (wr / rd examples) | cycles for 65,535 bl4 bursts | fraction of the ceiling |
|---|---|---|---|
| ceiling | 582.8 | 359,838 | 1 |
| step | 565.5 .. 565.8 | 370,775 | 32 / 33 (1.0304) |
| drop | 518.1 .. 521 | 404,238 | 8 / 9 (1.123 .. 1.125) |

Plus small single-pass levels at 580.0, 581.7, 582.0 .. 582.6 (one slot in
206, 510, 730). The levels are the same at bl4, bl8 and bl16, so they are a
rate, not a per-burst cost. Which direction of which cell takes which level is
a draw per pass.

## 2. The model: 584.6 on every phase

`model_issue007_go_sweep_granite_sku100_bi_2026-11-23.csv`: `granite_sku100_bi`
on `row_major_bl4`, `row_major_bl8`, `incremental_bl8`, 40 GO offsets of one
tREFI (0 .. 1521 CK, 39 apart): 584.6 / 584.6 on all 120 directions, to the
decimal. The mechanism is not in the model.

## 3. The proxy: the levels appear, as segments of a slower cadence

`row_major bl4`, 2,048 bursts per pass (~11,300 cycles, 14 refreshes per
pass at tREFI 780, the board's value at 100 MHz; the proxy's default 585 is
the 75 MHz board's), `TEST_TREFI` moved by one cycle at a time:

| tREFI | wr / rd MB/s | the slow segments (cycles per column, x columns) |
|---|---|---|
| 780 | 575.5 / 564.7 | 1.497 x504 (write pass); 1.625 x465, 1.622 x466 (read pass) |
| 781 | 580.5 / 578.3 | none |
| 779 | 549.7 / 580.1 | 1.497 x504, 1.624 x466, 1.750 x433, 1.625 x465 -- four in a row (write pass) |
| 782 | 580.8 / 579.6 | none |
| 778 | 571.4 / 581.6 | 1.497 x504, 1.496 x505 (write pass) |
| 776 | 579.0 / 580.0 | none |
| 784 | 585.7 / 578.2 | 1.250 x608, 1.250 x608 (a FASTER segment, write pass) |
| incremental bl8, 780 | 565.8 / 534.9 | 1.497 .. 1.499 x505 x6, 1.453 x520 x2 (write), 1.625 x466 x6 (read) |

Every other segment of every run is 1.332 .. 1.333 cycles per column; the gap
around every refresh is 24 .. 28 cycles whether the stream is in the base
cadence or a slow one. So the refresh costs the same every time; what a
refresh CAN do is re-launch the stream into another periodic orbit, which then
runs for one or several refresh periods.

The orbits, from the command dumps (bank b's ACT on the lane as `ACTb'`, its
column with auto-precharge `RDb AP`; eight banks rotate, every column at ACT +
2, every ACT on the lane in every segment):

| cadence | the period | the pattern | board level |
|---|---|---|---|
| 1.333 (base) | 3 columns per 4 cycles | `col+ACT, ACT, col+ACT, col` -- column gaps 1, 1, 2 | 583 (= 1.333 x 1.033 refresh) |
| 1.500 (9/8 of base) | 8 columns per 12 cycles | two 4-column bursts' ACTs at 0, 1, 2, 4, 5, 6, 8, 9, then nothing at 10, 11 | 519 (8 / 9) |
| 1.625 (39/32) | 8 columns per 13 cycles | the same with a three-cycle hole | -- |
| 1.750 (21/16) | 8 columns per 14 cycles | ACT gaps 3 and 4 inside the pair | -- |
| 1.250 (15/16) | 4 columns per 5 cycles | tFAW-exact: four ACTs in five cycles | 585.7 wr at tREFI 784 |

In the 1.5 orbit the first ACT of the next burst pair waits five slots past
the bank's readiness (tRC 6, the self-close's tRP_AP 1 / 2) for its head: the
head is not there. It is not the pool and not the generator's window
(section 4). The board's step level 566 has no orbit in these runs; a mixture
or an orbit these eleven refresh phases did not reach.

Why a pass holds one level for 461 refreshes: tREFI 780 is a multiple of the
base orbit's period (4) and of the 1.5 orbit's (12) and the 1.625 orbit's
(13), so once in an orbit every refresh lands on the same phase of it and
re-launches the same orbit; 14 (the 1.75 orbit) does not divide 780 and that
orbit lasted one segment on the proxy. On the proxy with tREFI 779 the phase
walks one cycle per refresh and the slow orbits chained for four periods; at
781 / 782 the walk never reached a launching phase in 14 refreshes.

## 4. What it is not

The same run (row_major bl4, tREFI 779, the four-segment slow stretch):

| variant | wr / rd | slow segments |
|---|---|---|
| as built (pool 16, generator window 32) | 549.7 / 580.1 | 1.497, 1.624, 1.750, 1.625 |
| `TEST_NUM_ENTRIES=32` (pool 32) | 581.8 / 545.7 | 1.625 x3 and 1.645 (read pass) |
| `TEST_MAX_OUT=8` | 549.7 / 580.5 | identical to as built |
| `TEST_MAX_OUT=4` | 495.6 / 495.5 | latency-bound, no segments |
| `TEST_MAX_OUT=2` | 252.3 / 250.0 | latency-bound |

Doubling the pool moves the slow orbit to the other pass; capping the window
at 8 changes nothing. The orbit is the pick pipeline's (request register,
winner, hint, lane, stale mask, row image) against the eight-bank rotation,
re-phased by the refresh drain, and the model's pipeline has the base orbit
only.

## 5. What this settles and what is next

- The issue's step 1: the model never shows the levels. Step 2: the proxy
  does, as orbits, with the stationarity rule above for why a pass keeps one.
- Step 3 is a model term only after the orbit's RTL state is read: the next
  probe is `PERF_PICK_PROBE` on the proxy at tREFI 779 across the refresh
  exit at cycle 63,260 (into the 1.497 segment) against the exit at 62,481
  (back to base), 160 cycles each -- which register of the pick core differs
  between the two re-launches. Then the model carries that state, or the
  RTL takes the base orbit deterministically (an RTL question for the pick
  core if the slow re-launch is a hold it need not take).
- The cells' tolerance: the drop is 11 percent on one direction per run, the
  step 3 on ten; the preset is not the shipped SKU. Priority stays P3; the
  task is filed as memory-controllers MC-023 together with the model's other
  open term (the record's addendum of 2026-11-23 to MC-020).

## 6. Record

- Model: `model_issue007_go_sweep_granite_sku100_bi_2026-11-23.csv` (120 rows).
- Proxy: `TEST_FPGA_CLK_HZ=100000000 TEST_T_PHY_WRLAT=1 TEST_TXN=2048 TEST_NUM_ENTRIES=16
  TEST_DUAL=1 TEST_PAGE_POLICY=2 TEST_ADDR_SCHEME=2 TEST_NUM_GEN=1 TEST_FAMILIES=row_major
  TEST_BURST_LEN=4 TEST_TREFI=<n> PERF_DRAM_TRACE=... PERF_DUMP=...` on
  `test_granite_char_perf.py::test_granite_char_perf`; 13 runs, 0 mismatched
  beats, 40 .. 60 s each (the pool-32 variant builds its own sim tag).
  Traces and perf dumps in the session scratch (not committed; the segment
  tables above are their reading).
- Tool: `projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/bin/dram_trace_segments.py`.
