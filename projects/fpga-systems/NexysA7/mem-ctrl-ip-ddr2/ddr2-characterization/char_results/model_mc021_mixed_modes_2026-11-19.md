# Model: the open-page mixed cell's two modes are the refresh phase at GO, and the model has both once the record's hit flag lags on the way down (memory-controllers MC-021 step 8), 2026-11-19

`open_page mixed_bl8` (four writers and four readers on two banks, rows eight
apart, open page) was the one cell the board-compare still called out after
step 7: the board gives it in two modes -- 311 / 522 (union 622) on three runs
of five, 272 / 272 (545) on two -- and the model gave 276 / 276. This record
settles what the two modes are, what picks one, and makes the model show both.

| run | mode | write / read MB/s (union) |
|---|---|---|
| board, 3 of 5 windows runs | fast | 311 / 522 (622) |
| board, 2 of 5 | slow | 272 / 272 (545) |
| proxy, tREFI 770 / 773 | fast | 317 / 477 (634), 307 / 418 (614) |
| proxy, tREFI 771 / 772 / 774 / 776 / 780 | slow | 245-274 / 246-304 |
| model, 6 of 40 GO phases (close_lag 2) | fast | 309 / 547, 303 / 496, 313 / 446, 303 / 418 |
| model, 34 of 40 | slow | 274 / 276 |
| model, any phase, close_lag 0 (step 7) | slow only | 274-278 / 276-289 |

## 1. The proxy has both modes, and the refresh phase picks

The granite proxy is seeded once for every run (`PERF_SEED`), so three runs of
the cell are identical (274 / 304). What varies between board runs with a
hardware GO is the refresh counter's phase at GO. Sweeping the refresh period
(`TEST_TREFI`) by a few cycles moves that phase: 770 and 773 land in the fast
mode, 771, 772, 774, 776 and 780 in the slow one. The two runs are identical
cycle for cycle from GO until the first refresh falls (at GO + 51 in the fast
run); after that they diverge.

## 2. What the two modes are

From the direction-flip logs and the DRAM traces of the fast (tREFI 770) and
slow (772) runs, with the pick probe anchored across GO (`PERF_PICK_PROBE_FROM`)
and at the first zero-column turn:

- **Slow**: the register alternates at the batch cap -- read turns of 255
  columns in about 330 cycles, write turns of 255 in about 417 (the write
  column after a read pays the turnaround), both directions sharing the window
  to the end. 116 of 127 flips are cap flips.
- **Fast**: the read turns are the same 255-column cap turns, but 48 of the 63
  write turns last 10 cycles and fire no column: the register flips to the
  writes at the cap, and a read column takes it straight back (cause 0). The
  writes are starved until the reads finish (the read window shrinks from
  43k to 27k cycles at 512 bursts), then run alone. Both runs contain both
  kinds of write turn; the fast run has 48 zero-column turns, the slow 7.

## 3. The zero-column write turn, cycle by cycle

Probe at the fast run's first one (GO + 11,581 .. 11,641). Bank 0 is the
contested bank: the lane has just opened the WRITE's row there (cycle 11,588)
beside the reads' columns, and the write column request shows at 11,591. The
reads' bank-0 head misses that row, and its PRE request comes up when tRAS
from the lane's ACT allows (11,592), the same cycle the read batch reaches 255.
Then:

- 11,593: the register flips to the writes; the reads' PRE fires in that
  cycle and closes bank 0 -- the write's row, which the write's head was
  hitting.
- 11,594: the write head still reads as a HIT (the registered row image); its
  column is the winner and waits on the turnaround. 11,595: the request is
  gone (the record re-classified); the reads' own ACT request for bank 0 is
  live (their PRE + tRP). 11,596: the reads' ACT fires on main -- bank 0 is
  the reads' row again. The write head's ACT request appears at 11,596, one
  cycle too late, and now needs a PRE first.
- The write's PRE can fire at the reads' ACT + tRAS = 11,601, when the
  write direction's idle counter reads 8: the idle hold has lapsed, `w_xdir_ok`
  is true, the select takes the reads' column for 11,602, it fires, and the
  register flips back (cause 0) with the write batch at 0.

In the normal write turn (GO + 329) the same chain runs one cycle earlier:
the reads' PRE fires the cycle BEFORE the flip (the cap landed a cycle later
relative to the lane's ACT), the write's PRE lands at idle 7, inside the hold,
and the writes keep the register for their 255. One cycle, and the regime. The
refresh at GO + 51 shifts the stream by a few cycles, and from then on the cap
count's phase against the lane's ACT -- which is set by everything before --
decides each turn.

## 4. What the model lacked: the hit flag on the way down

The model's `hit_lag` (step 4) delays a head's HIT after an ACT by two slots
(the bank timers' registered row image, the record's hit flag, the request
register). It read the row image live on the way DOWN: a head whose row a PRE
closed requested its ACT one slot after the PRE, where the RTL takes three
(the stale column still shown at +1, nothing at +2, the ACT request at +3).
So at a cap flip the model's write head re-activated BEFORE the reads' hinted
re-ACT, every time, and no phase could produce the zero-column turn.

`close_lag` (default 2 = `hit_lag`): a head whose row a PRE closes while it
reads as a hit requests its ACT `close_lag` slots after the PRE
(`m_pair_closed_clk`, marked at a main or lane PRE for every pair of that bank
whose head is a column). With it, and the model's GO swept against its refresh
phase (`GRANITE_GO_OFFSET`, the trace frontend's new `start_tick`), 6 of 40
phases give the fast mode with the RTL's structure (56 of 63 write turns
zero-column, 7 cap turns, against the proxy's 48 and 15) and 34 the slow one;
with `close_lag` 0 every phase is slow. The three cells that fixed the earlier
terms do not move (bank_interleave col_major_bl4 283 / 389, close_page
col_major_interleaved_bl16 172 / 239, close_page mixed_bl8 56.3 / 57.5).

## 5. What this means for the compare

The board-compare takes one number per cell, so the open_page mixed row is
whichever mode the board's `windows` run of the day landed in (the s4 set:
fast). Against the fast mode the model's fast phases are within tolerance
(309 / 547 against 311 / 522, union 856 / 833, +2.8 percent... the union
of the board's fast mode is 622 against the model's fast phases' 729-856 at
512 bursts, a count effect: the model's fast mode at the board's 32,000
bursts is what the full run reports); against the slow mode the model's slow
phases are 274 / 276 against 272 / 272. The cell is in on both modes by mode.
The full compare of the three configs against the step-5 board set: 56 in / 1 out, the one out
the open_page mixed row against the board's fast-mode number (the model's
default GO phase gives the slow mode, 274 / 274 against the board's slow
272 / 272; the fast phases give 303-313 / 418-547 against 311 / 522); one
cell moved more than half a percent from step 7 (`defaults mixed_bl8` 276 ->
274, toward the board's 272 / 273).

The proportion differs: the board fast on 3 of 5 runs, the proxy on 2 of 7
refresh periods, the model on 6 of 40 phases. The model's phase sweep is a
uniform sample of the refresh phase; the board's five GOs are not, and five
is too few to call a proportion. What the three agree on is the pair of modes
and their numbers.

## 6. Record

- Proxy runs: `TEST_PAGE_POLICY=1 TEST_FAMILIES=mixed TEST_NUM_GEN=4 TEST_TXN=512`
  with `TEST_TREFI` in {770, 771, 772, 773, 774, 776, 780}, `PERF_DIR_FLIPS`,
  `PERF_DRAM_TRACE`, `PERF_PICK_PROBE` (`PERF_PICK_PROBE_FROM` 189,700 /
  197,800 across GO; 201,700 at the first zero-column turn).
- Model: `granite_sku_controller.cpp` (`m_close_lag`, `m_pair_closed_clk`,
  `note_close`), the trace frontend `timed_loadstore_trace.cpp` (`start_tick`),
  `char_model.py` (`ModelConfig.close_lag`, `sku_closelag0`, `GRANITE_GO_OFFSET`),
  `test_char_model.py` (`test_close_lag_gives_the_open_page_mixed_cell_its_second_mode`).
  40 / 40 and the vendor's 217 pass.
- Previous steps: `model_mc021_admission_gates_2026-11-19.md` (step 7),
  `model_mc021_wr_fill_lag_2026-11-19.md` (step 6).

## 7. The compare read by mode (close-out, 2026-11-19)

The owner's decision on section 5's one row: read a bimodal cell by mode, the
model's default phase stays 0. `board-compare --board-also <reruns>` groups a
cell's board runs into modes within the tolerance of each other, takes one
`--model` CSV per model GO phase (`run` writes `GO offset N` into the row's
notes when `GRANITE_GO_OFFSET` is set), and needs every board mode matched by
a model run with no model run in a mode the board never showed. The SKU's
mixed cell at GO offset 480 at the board's count: 309 / 568, union 618
(`model_ramulator2_ddr2_granite_sku100_s8_go480_2026-11-19.csv`).

`compare_model_sku_vs_board_sku100s4_s8_modes_2026-11-19.md`, the s8 model set
plus that run against the board's five windows runs: **56 in / 1 out**.

| preset | board, by mode | model, by phase | delta by mode | verdict |
|---|---|---|---|---|
| open_page mixed_bl8 | 311 / 522 (union 622) x3; 272 / 272 (545) x2 | 274 / 274 (547) GO 0; 309 / 568 (618) GO 480 | -0.7; +0.4 % | IN |
| defaults mixed_bl8 | 272 / 273 (545) x5 | the same two | +0.5 % and a model mode the board never showed | OUT |
| the other seven windows cells | five runs within a point, one mode | one run | as the s8 compare | IN |

The out moved, and it is a finding: `defaults` is the hybrid page predictor,
which the model runs as plain open page (the same `granite_sku100`
configuration as `open_page`). On this cell the board's predictor stayed in
the slow mode on all five runs where `open_page` was fast on three; at that
proportion five slow of five is about a one-percent draw. Filed as
memory-controllers ISSUE-006 (more board runs settle draw against predictor;
if the predictor, its rule becomes a model term). The slow attractor itself
-- the fast mode is better on both directions and the union, and the pick
core takes one or the other on the refresh phase -- is filed as ISSUE-005, a
design question outside MC-021.
