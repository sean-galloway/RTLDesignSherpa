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
