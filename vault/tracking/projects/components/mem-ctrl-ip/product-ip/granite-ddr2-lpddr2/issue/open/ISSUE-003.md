# ISSUE-003: the granite perf proxy is not run-to-run deterministic -- the same build directory, seed and environment give cycle counts up to 0.4 percent apart

> Source: memory-controllers MC-019's proxy A/B, 2026-11-20
> (`char_results/rtl_mc019_lane_act_only_2026-11-20.md`, section 5).

**Priority:** P3 -- it does not fail a test; it sets the floor under which a
proxy delta cannot be read from one run against one run.
**Status:** open 2026-11-20
**Owner:** TBD

## What was seen

`test_granite_char_perf` at the SKU (100 MHz, lane, pool 16, 4 generators,
512 transactions, AxLEN 8, five families) with TEST_DUAL=0, run twice in the
same build directory with the same seed (2882343476) and environment:

| family | run 1 wr / rd cycles | run 2 | delta |
|---|---|---|---|
| incremental | 17412 / 17416 | 17412 / 17416 | 0 |
| row_major | 17322 / 17331 | 17347 / 17328 | 0.14 % |
| col_ilv | 17918 / 18353 | 17992 / 18386 | 0.4 % / 0.18 % |
| col_major | 19530 / 19507 | 19524 / 19507 | 0.03 % |
| mixed | 49872 / 49519 | 49740 / 49387 | 0.26 % |

The first run shared the machine with three other sims and a Vivado run, the
second with less. The same RTL in two directories gave `col_major` 752.4 and
758.8 MB/s on the write side (0.85 percent). MC-021 step 8 had observed three
reruns of a single-family (`mixed`) run identical to the cycle; a five-family
run is not. A first MC-019 A/B that compared a `git archive` of HEAD against
the working tree read this band as the RTL change (the TEST_DUAL=0 pair,
which the change cannot reach, differed on four of five cells) until the two
forms were run in one directory.

## The question

What in the harness depends on anything but the seed? The host program runs
over a simulated UART with the sim's own clock, so the suspect is anything
paced on the wall clock -- a timeout, a poll interval, a retry -- that lands
GO (or a pass's first beat) on a different cycle against the refresh counter
when the machine is loaded. `incremental` being identical both times and the
others moving by tens of cycles fits a shifted start, not a different stream.

## What settles it

1. Three runs each under load and idle, with the first-beat cycle of every
   pass logged (the perf dump's `wr_cycles` / `rd_cycles` are durations; the
   start cycle is what should be compared): a start that moves names the
   harness; a start that holds and a duration that moves names the DUT (and
   then a seed it does not report).
2. The wall-clock dependence removed from the harness (sim-time pacing), and
   the three runs identical to the cycle.
3. Until then: a proxy delta under about 0.5 percent needs repeats, and an A/B
   is two RTL forms in ONE directory, never two directories.
