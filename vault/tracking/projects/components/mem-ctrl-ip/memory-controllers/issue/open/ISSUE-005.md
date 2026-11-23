# ISSUE-005: the open-page mixed cell has a slow attractor -- the direction register's 255 / 255 cap alternation at 272 / 272 where the fast mode runs 311 / 522 -- and the pick core takes one or the other on the refresh phase at GO

> Source: memory-controllers MC-021 step 8, 2026-11-19
> (`char_results/model_mc021_mixed_modes_2026-11-19.md`). Filed at close-out
> on the owner's decision: an observation about the design, not the model.

**Priority:** P3 -- the shipped SKU (`defaults`, the hybrid page predictor)
shows neither mode's race on the board (five of five runs at 272 / 273, see
ISSUE-006); this is the `open_page` preset, and it is a throughput
opportunity, not a correctness question.
**Status:** open 2026-11-19
**Owner:** TBD

## The question

On the board's `open_page mixed_bl8` cell (four writers and four readers from
one GO, rows apart in shared banks) the granite pick core lands in one of two
self-consistent modes for the whole cell, decided at GO by the refresh
counter's phase: three of five runs at 311 / 522 MB/s (union 622), two at
272 / 272 (545). The proxy reproduces both when `TEST_TREFI` is moved a few
cycles, the model when its GO is swept against its refresh phase
(`GRANITE_GO_OFFSET`, 6 of 40 phases fast).

The fast mode is the direction register ping-ponging on zero-column write
turns: at the cap flip the holder's PRE closes the row the lane had just
opened for the waiting write, the waiter's head takes three cycles to read as
a miss, the holder's hinted re-ACT takes the bank first, the waiter's re-PRE
lands with the idle counter at 8 and a read column takes the register back
(48 of 63 write turns on the proxy). The reads run nearly alone to the end,
then the writes run alone. The slow mode is the 255 / 255 batch-cap
alternation, both directions sharing every window. One cycle in the cap
flip's phase against the lane's ACT picks each turn.

The fast mode is better on both directions and on the union (+14 percent),
and the cell's writes also finish sooner (2.64 M cycles against 3.01 M). The
question is whether the pick core should take it deterministically -- a rule
for the zero-column turn or for the PRE courtesy at the cap flip that does
not depend on the refresh phase -- and whether the fast mode's shape (the
writes starved while the reads drain) is acceptable fairness for a controller
whose other presets never show it.

## What settles it

1. A candidate rule priced in the SKU model first (`char_model.py`, the
   `GraniteSKU` controller), across the GO-phase sweep: it must give the fast
   mode on every phase of this cell and move no landed cell outside its
   tolerance.
2. The proxy with `TEST_TREFI` at a slow period (771, 772) and a fast one
   (770, 773) under the candidate: both fast, the flip log's turn structure
   as the model's.
3. The RTL change through the pick core's gates: the formal gold copy with a
   dated note, equivalence / cover / dual, `TEST_DUAL` both ways, the
   `GRANITE_SYS_100=1` bitstream closing under the 0.2 ns budget, the board
   re-run on every preset.
4. Or a recorded no-action: the `defaults` preset does not enter either race
   (ISSUE-006), so the SKU as shipped does not pay for the slow mode.

> 2026-11-20, ISSUE-006 closed: with the RTL's hybrid page policy in the model
> the `defaults` mixed cell is one mode at every one of 40 GO phases (the
> board's five of five); the race this issue names forms under `open_page`
> (policy_mode 0, the flat close-on-drain), where the model shows the fast
> mode on 2 of 40 phases and the board on 3 of 5 runs. The shipped preset does
> not enter it; this stays a question about the open-page configuration.

> 2026-11-22, the phase-exact counters became the host default (MC-020
> decision 1, `char_results/board_mc020_default_phase_exact_sku100_2026-11-22.md`).
> The modes moved with the counters: the board's `open_page` cell is 280 / 280
> (slow, two of three runs) or 303 / 594 (fast, one of three); `defaults` 277 /
> 276 three of three (one mode, as before). The model's preference INVERTED:
> at its default (`DDR2_GRANITE_SKU100_PX`) it is in the fast mode at both GO
> phases 0 and 480 on `defaults` (310 / 571) and on `open_page` (308 / 521),
> where under the margin it never left the slow mode on `defaults` and showed
> the fast one on 2 of 40 phases on `open_page`. So the shipped preset's mixed
> cell is now the one where the model is in the wrong mode on every phase
> tried (+11.8 percent on the union against a 10 tolerance; the compare's
> three OUT mixed cells). The question this issue asks is unchanged -- which
> mode the pick core should take, deterministically -- and the model now needs
> the 40-phase sweep at the new counters before it can price a rule.

> 2026-11-22, later (MC-020 decision 2,
> `char_results/board_mc020_t_rp_ap_sku100_2026-11-22.md`): the inversion
> above was not the direction register. The model's auto-precharge path took
> the DRAM's CK-exact distance where the RTL sequences tRAS (or the column's
> recovery) then the same tRP; with the RTL's sequence as a term (`ap_seq`,
> the shared tRP) and no RTL change, the `defaults` mixed cell is one mode
> again, 290 / 343 (union 581 against the board's 553 x3, in at +5), and the
> `close_page` mixed cell lands exactly (60 / 66). Only the `open_page` cell
> keeps the inverted preference (model 617 at GO 0 and 480, board 559 three of
> three): the question this issue asks is that cell's, under `open_page`, as
> it was on 2026-11-20. With the TIMINGS_RP_AP field (the RTL step) the model
> prices `defaults` mixed at 619 and `close_page` mixed at 146 -- the board on
> the step's bitstream says which mode each takes (section 5 of the record).
