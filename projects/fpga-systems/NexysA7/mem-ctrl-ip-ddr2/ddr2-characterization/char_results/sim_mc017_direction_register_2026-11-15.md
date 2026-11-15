# The direction register on the `mixed` window: the waiting direction got the bus for five cycles and no columns (memory-controllers MC-017, sim half, 2026-11-15)

MC-016 closed with granite's `mixed` cells 20-24 percent under the model's
strict per-bank FIFO at the same pool depth, a read that waited 52 000
cycles, and the direction register named as the mechanism. This is the
measurement and the fix, in sim. Same point as MC-014/15/16: granite perf
proxy, 100 MHz MC / CK 200, DFI 1:2, x16 BL4, `t_phy_wrlat` 1, tREFI 772,
TEST_TXN 1024; `mixed` = four writers and four readers from one GO, rows 8
apart in shared banks, four injectors. Cells are write / read MB/s over each
direction's own window; the **union** is both directions' bytes over the
longer window (the proxy's `mixed_bw_mb_s`, the board CSV's "union").

## 1. The flips, counted

`PERF_DIR_FLIPS=<path>` (new in `test_granite_char_perf.py`) logs every flip
of the pick core's direction register with the cause it records (0 = a
column of the other direction fired, 1 = the held direction drained, 2 =
the batch cap) and the column batch that ended, and sums the holds per
direction. The window at pool 8, lane on, cap 255 (`GRANITE_DIR_BATCH_MAX`):

| direction | holds | holds with ZERO columns | holds with columns | cycles in those | columns | cycles / column |
|---|---|---|---|---|---|---|
| reads | 143 | **136** (5 cycles each, median) | 7 | 2 151 | 1 785 | 1.21 |
| writes | 143 | 6 | 137 | 52 203 | 32 677 | 1.60 |

Pool 16 is the same shape (136 of 145 read holds empty). The writes hold the
bus for 255 columns (cap), the cap hands the register to the reads, and five
cycles later a write column fires and takes it back with a fresh batch of
255 -- 136 times in a row. The reads get their 32 768 columns after the
writes finish: the window is sequential, not mixed, and the read side's
`rd_lat_max` of 52 120 cycles is the write side's whole run. (The board's
bimodal cells -- `defaults` 487 / 300 and `open_page` 334 / 649 at pool 8 --
are the two orders this can land in.)

## 2. The batch cap is not the lever

Sweeping the cap (`TEST_DIR_BATCH_MAX`, threaded `granite_top_geared
.DIR_BATCH_MAX` <- `granite_char_macro` <- `granite_char_harness` <- the TB
top, default the package's 255 -- bit-identical; `GRANITE_DIR_BATCH_MAX` is
the board-build knob beside `GRANITE_NUM_ENTRIES`):

| cap | pool 8 wr / rd (union) | zero-column read turns | pool 16 wr / rd (union) | zero-column read turns |
|---|---|---|---|---|
| 255 | 477 / 301 (601) | 136 of 143 | 473 / 267 (533) | 136 of 145 |
| 128 | 396 / 292 (584) | 2 038 of ~2 080 | 423 / 264 (528) | 2 028 |
| 64 | 495 / 302 (603) | 2 017 | 448 / 265 (530) | 2 034 |
| 32 | 252 / 227 (455) | 1 181 | 493 / 265 (531) | 2 018 |
| 16 | 464 / 295 (590) | 2 049 | 464 / 260 (520) | 2 049 |

A smaller cap flips more often (the batch histogram moves to 16, the pool's
two bursts) and the reads still get nothing on each turn: the take-back is
independent of the cap. No SKU default to propose from this axis.

## 3. The take-back, cycle by cycle

`PERF_PICK_PROBE` gained a start at the n-th flip (`PERF_PICK_PROBE_FLIP`:
the absolute cycle of a window moves between runs, the flip count does
not) and the lane's state. At a cap flip, with the lane on:

1. In the cycle the cap flips (write batch 255, a read column request
   visible), the writer's PRE on the shared bank is firing: with
   `DIR_OWNS_ROWS` the owner may close the other direction's row, and the
   read's column request is a cycle stale. The read column is picked, then
   dropped (its hit is gone).
2. The reads now need PRE / ACT; their row request is a decode cycle
   behind. The writer's ACT request on the same bank is not, and the row
   fall-through (no preferred row request -> any row) fires it: the bank
   re-opens on the writer's row.
3. The writer's ACT hints its column (the short-hop ACT -> COL chain) and
   the hint sits at the top of the select, ungated by the direction
   register. It fires: cause 0, the register follows it, batch 1 of a new
   255.
4. With the hint gated (first fix), the same five cycles end in the
   "drained" flip instead: the reads have no column PENDING (closed rows)
   while the writer has one ready, and that branch read as "drained". With
   the drain flip under the idle hold (second fix), the reads' first
   command -- the PRE of the bank the writer's row held -- fired in the
   cycle the eight-cycle hold ran out, one cycle late: the lane on costs the
   read turn two cycles to the stale column, three to the writer's ACT.

## 4. The fix, in `mc_bank_pick`

Four terms, every one a register-only AND on an existing decision:

- a COLUMN hint of the direction that does not hold the register obeys
  `w_xdir_ok`, the gate the plain column set already obeys (row hints are
  not touched: the row preference mask orders them);
- the drain flip of the direction register waits while `w_dir_hold_idle`
  holds (queued heads, a command fired within `DIR_HOLD_IDLE` = 8 cycles),
  the term that already gated the other direction's columns;
- "drained" also requires no live row request of the held direction and no
  row command of it in the winner register (its request bit is stale-masked
  while picked);
- the lane's "a column is pending somewhere" (which masks a held lane row
  from the main select) counts only columns the gate lets fire: the held
  direction's, or the other direction's when `w_xdir_ok` (split per
  direction in the lane's register-only block, combined in the select).

One more was tried and reverted: gating the row fall-through while the
register is held made the window fair but took the lane-OFF `mixed` union
524 -> 321 -- the other direction's row commands under the holder's columns
ARE the lane-off form of the row lane. It stays as it was.

The golden copy of the pick core (`formal/mc_common/mc_bank_pick/`) carries
the same three main-slot changes with a dated note (the lane change is inside
`DUAL_ISSUE`, which the copy predates and the equiv tasks compile out);
`equiv`, `equiv_n4`, `cover`, `dual`, `dual_cover` pass on every iteration.

## 5. Results

`mixed`, the probe's flip summary beside each cell:

| point | before: wr / rd (union), `rd_lat_max` | zero-col read turns | after: wr / rd (union), `rd_lat_max` | zero-col read turns |
|---|---|---|---|---|
| pool 8, lane on (board SKU + lane) | 475 / 300 (601), 52 120 | 136 / 143 | **272 / 273 (545)**, 520 | 0 / 128 |
| pool 16, lane on (MC-015's point) | 473 / 267 (533), 52 860 | 136 / 145 | **272 / 272 (543)**, 521 | 0 / 128 |
| pool 8, lane off (the shipped SKU) | 262 / 331 (524), 1 659 | -- | **264 / 265 (528)**, 529 | 0 / 128 |

Every turn now carries its 255 columns (256 cap flips and one short batch per
run); the two directions share the window to within 1 MB/s; the longest a
read waits is ~520 cycles (5.2 us at 100 MHz) where it was 52 000 (520 us).
The union is +1 percent at the shipped SKU, +2 percent at pool 16 with the
lane, and -9 percent at pool 8 with the lane: there the old behaviour ran the
writes alone (1.65 cycles per column against the reads' row-closing
interference) and then the reads alone at the pure column rate, and a fair
alternation pays ~255 turnarounds and the writers' per-burst row switch
(1.68 cycles per column) on every turn. The model (MC-016) said the same:
its strict FIFO at pool 8 is 750 for the symmetric case, and no symmetric
scheduler reaches the sequential 601 + 0's shape. A 520 us read starvation
is a defect on a memory controller; the trade is the owner's to confirm and
the board half measures it.

The single-direction families (lane on, pool 8 / 16; lane off, pool 8):

| family | before | after | |
|---|---|---|---|
| col_major_interleaved | 686 / 773, 766 / 768, 681 / 686 | 687 / 774, 767 / 769, 681 / 686 | |
| row_thrash | 687 / 775, 769 / 769, 684 / 687 | 687 / 773, 769 / 769, 684 / 687 | -2 on pool 8 lane on |
| random | 627 / 722, 719 / 717, 626 / 656 | 627 / 721, 719 / 715, 626 / 656 | -1 / -2 |
| col_major (control) | 414 / 516 | 414 / 517 | |

Within 2 MB/s everywhere; the lane-off cells are bit-close to the 2026-11-12
ones. The small lane-on read losses are at the write -> read pass boundary,
where the hint gate now holds a read column hint for the last write columns.
Zero mismatched beats in every run.

Regressions on the shared pick core (final RTL): granite top 25 passed /
5 skipped / 1 xfailed (the standing marks); pumice fub 32, macro 78, top
220 (4 skipped), phy 32 (4 skipped); common-ip store-arbiter contract bench
27 passed / 3 xfailed (standing) and the head-records contract; the char
framework func suite (see the task file for the final count).

## Method

- **Count the flips before touching the rule.** The direction register had
  three hypotheses on it (the cap, the hold, the courtesy); the flip log
  with cause and batch length said in one run that the cap was reached
  every time and the handover failed every time. The cap sweep -- the task's
  original item -- was then a two-line table confirming a non-lever.
- **A fix that holds one path opens the next.** Gating the hint moved the
  take-back to the drain branch; holding the drain moved it one cycle past
  the idle window. Each step needed the probe again, not a better guess:
  the lane-on residue was a one-cycle race between the register's decision
  and the fire that would have reset its idle counter.
- **Re-check the other build of the same block.** The fall-through gate
  looked right with the lane on and cost 40 percent with the lane off,
  because the lane-off design uses the main slot for what the lane does.
  Every pick-core change runs `TEST_DUAL` both ways from now on.
- **Fairness has a price on a synthetic window and the model prices it.**
  The sequential shape the old register produced is faster in aggregate
  than any fair schedule on this family; the number to carry to the owner is
  the union AND the worst wait, not one cell.

## Recipe

    cd projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tests   # env_python sourced
    export TEST_FPGA_CLK_HZ=100000000 TEST_T_PHY_WRLAT=1 TEST_TREFI=772 TEST_TXN=1024 TEST_LEVEL=FUNC
    # the flips (any family; mixed here), lane on, pool 8
    TEST_DUAL=1 TEST_NUM_ENTRIES=8 TEST_FAMILIES=mixed TEST_NUM_GEN=4 PERF_DIR_FLIPS=$OUT/flips.json \
        python3 -m pytest test_granite_char_perf.py::test_granite_char_perf -q
    # the cap sweep (own sim_build tag per cap and per pool size now: _b<N>, _n<N>)
    TEST_DUAL=1 TEST_NUM_ENTRIES=16 TEST_DIR_BATCH_MAX=64 TEST_FAMILIES=mixed TEST_NUM_GEN=4 python3 -m pytest ...
    # the pick's state from the 4th flip, 30 cycles, with the lane's registers
    TEST_DUAL=1 PERF_PICK_PROBE=$OUT/pick.json PERF_PICK_PROBE_FLIP=4 PERF_PICK_PROBE_CYCLES=30 python3 -m pytest ...
    cd formal/mc_common/mc_bank_pick && make all           # equiv, equiv_n4, cover, dual, dual_cover

Board half: `board_mc017_direction_register_sku100_2026-11-15.md`.
