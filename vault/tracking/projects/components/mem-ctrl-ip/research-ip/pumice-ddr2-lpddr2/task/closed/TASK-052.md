# TASK-052: head2's hit is the stored same-row bit; one head record per bank measured and rejected

> Source: report 5.11's closing line (TASK-051): "what is left in the store
> is the write-beat data path and the slot fields; the next structural step
> would be records without the slot-indexed age flag, or a single head record
> per bank, each a measured trade against the picker's post-pop streaming."
> Related: TASK-050 (the FIFO store), TASK-051 (payload by slot), the
> handbook note `design/per-bank-queues-admit-from-the-pool.md`.

**Priority:** P2
**Status:** closed 2026-10-24 (board +0.268 ns, 0 failing endpoints; granite_core 6 634 -> 6 105 LUT, 4 580 -> 4 572 FF; store 3 096 -> 2 627 LUT; every perf cell cycle-identical; the one-record variant measured at -25 to -50 percent and left as a knob, default off)
**Owner:** TBD

## What landed

- **`mc_bank_fifo_store`: the second record's `hit` is the stored
  same-as-previous bit of its queue position, not a row compare.** The pick
  core reads head2 only under its one-cycle pop shadow, the cycle after it
  fired the head as a column command. The record it reads then was formed
  while that column was firing, against a row image that showed the head's
  row open (a column fires only against a live-valid row the record
  classified as a hit; a PRE at t-1 clears row_valid, an ACT at t-1 needs a
  closed bank whose record could not have been a hit). So "head2's row ==
  the open row" is exactly "head2's row == head's row", which is the bit
  pushed with head2 (`r_wq_sp` / `r_rq_sp`). Auto-precharge on that column
  does not enter: the image the record was formed against predates it. The
  compare form was a 14-bit 8:1 row mux plus a 14-bit compare per record,
  sixteen records; the stored form is one bit already there. The head's hit
  is still the compare (its open row is set by whatever ran before it,
  including the other direction).
- **`HEAD2_EN` knob** (store, granite_core, granite_top_geared, the char
  macro / harness / top with `GRANITE_HEAD2_EN`, the UART tb top and the
  perf proxy with `TEST_HEAD2_EN`, both `create_project.tcl` hooks): 0 =
  one head record per bank; head2 outputs are constant 0 and the pick core
  idles a pair for the cycle after each of its column fires. Default 1.
  Measured below; it is a knob so the number can be retaken, not a variant
  to carry.

## Measured

Board (Nexys A7, 75 MHz, four injectors, LUT / FF; sub-block rows are
Vivado's post-route attribution):

| build | granite_core | store | sched plane (pick, timers) | WNS |
|---|---|---|---|---|
| TASK-051 committed (payload by slot) | 6 634 / 4 580 | 3 096 / 2 090 | 1 671 (797, 522) | +0.194 ns |
| **head2 hit from the stored bit (this task, the committed text)** | **6 105 / 4 572** | 2 627 / 2 082 | 1 665 (769, 507) | +0.268 ns, 0 / 109 381 |
| + `HEAD2_EN = 0` (one head record per bank) | 5 824 / 4 452 | 2 207 / 1 962 | 1 802 (929, 501) | +0.195 ns, 0 / 109 145 |

Against the 5.10 baseline (9 956 LUT) the product core is now 39 percent
smaller at the same bandwidth.

Perf (granite proxy, board geometry, 75 MHz, wr / rd MB/s, mismatched 0 in
every cell; "identical" = equal to the committed grid to the decimal, same
cycle counts):

| family | threads | stored-bit hit (committed) | one head record per bank |
|---|---|---|---|
| incremental / row_major / col_ilv / col_major | 1 | identical (568.2 / 567.5, 576.5 / 572.2, 460.8 / 451.2, 311.1 / 357.7) | 292.1 / 292.5, 288.7 / 287.7, 408.8 / 453.0, 212.4 / 231.7 |
| incremental / row_major / col_ilv / col_major | 8 | identical (556.9 / 555.3, 557.6 / 557.2, 533.5 / 525.9, 459.0 / 457.7) | 410.7 / 445.5, 409.8 / 441.4, 392.5 / 425.8, 414.3 / 457.4 |
| row_thrash, 8-beat bursts | 1 | 310.0 / 354.6 (no grid cell at this burst length) | 211.9 / 231.5 |
| row_thrash, 2-beat bursts | 1 | identical (128.7 / 162.9, 2 386 / 1 886 cycles) | 116.6 / 142.4 |
| random | 8 | identical (442.1 / 452.9) | 357.5 / 402.4 |
| mixed (concurrent, 2 threads per bank) | 8 | identical (98.1, 200 290 / 200 299 cycles) | 98.3, 199 914 / 199 909 cycles (flat: that family is turnaround-bound, not shadow-bound) |

**The one-record variant is a no at this geometry**, not a single-thread
corner: at BL4 x16 an 8-beat AXI burst is eight same-bank entries, so the
pop shadow is the common case, and the variant halves the single-bank stream
(292 vs 568) and loses 20 to 26 percent at eight threads, for 281 LUT off
the core (the pick core's attribution grew by 160 with the constant-zero
second record). The second record stays.

**Not taken: records without the slot-indexed age flag.** The flag costs
sixteen 16-bit timestamps, sixteen subtract-compares against
`sched_age_thresh` and thirty-two 1-bit 8:1 lookups (of the order of 250 FF
and 200 LUT in the store). It is the `SCHED_POLICY.order_mode =
age_threshold` anti-starvation hook, a CSR-visible product feature, so a
compile-out would be a knob like `HEAD2_EN`, default on; worth a build if
the owner wants the number, not a change to the default.

## Gates

Contract battery 12 passed / 3 strict xfailed (entry + fifo cells); granite
suite 6 / 1 xfailed on the FIFO store, with `HEAD2_EN = 0`, and on the entry
store (the entry run checked to have compiled `STORE_BACKEND = 0`); lint of
granite_core default / `HEAD2_EN = 0` / `STORE_BACKEND = 0` / `NUM_ENTRIES =
1` and of the whole `granite_char_harness` default and `HEAD2_EN = 0` (0
errors). Pumice does not instantiate the FIFO store and the plane and pick
core are untouched; its 218 / 218 from TASK-051 stands on this text. Board
build md5 of `mc_bank_fifo_store.sv` == the committed text.
