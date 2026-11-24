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

> 2026-11-23 (`char_results/model_issue005_hold_idle_modes_2026-11-23.md`): the
> 40-phase sweep at the phase-exact counters and the field. `open_page`: the
> board's pair (280 / 280 x26 phases, 308 / 524 x14; the board 8 slow / 2 fast
> of ten runs). `defaults`: three model modes (280 / 280 x14, 290 / 343 x22,
> 305 / 489 x4) where the board is 277 / 276 ten of ten -- a fidelity gap on
> the shipped preset, to MC-023. The mechanism, slot by slot: at the batch cap
> the holder's ownership PRE (requested one slot before the cap) closes the
> waiter's row; the waiter's head reads as a hit for close_lag, the holder's
> hinted re-ACT takes the bank, the waiter's re-PRE lands against the idle
> counter -- at idle 8 a cross-direction column takes the turn (the fast
> mode), at idle 7 the waiter's PRE fires first (the slow). One slot, placed
> by the refresh phase. Candidates priced across the 40 phases on both
> presets: DIR_HOLD_IDLE 0 / 4 / 6 / 9 / 10 / 12 / 16 and DIR_OWNS_ROWS off.
> **No value gives the fast mode on every phase** (the read-first shape
> appears at hold 0 / 4 / 6 with other phases in another mode); hold >= 9
> gives the time-share on 40 / 40 phases of both presets (union 560, the
> board's `defaults` 10 of 10 and `open_page` 8 of 10), at the cost of the
> close_page mixed cell's read-first shape (73 / 121 -> 61 / 61, -16 on the
> union; 55 in / 2 out against the SKU board set) and the open_page fast
> phases' 617. The decision is the owner's: build GRANITE_SCHED_DIR_HOLD_IDLE
> 9 for a deterministic cell at that price, a recorded no-action (the shipped
> preset is one mode on the board), or a read-priority direction register,
> which is a design, not a knob, and is not priced.

> 2026-11-23, later (MC-023 item 2): the sweep above ran on a model with a
> defect in the self-close lookahead guard. On the fixed model the mixed
> cell is in the read-first fast mode on 40 / 40 phases of BOTH presets
> (`open_page` 308 / ~520, `defaults` 309 / ~565), so the model's two-mode
> race and the slot trace were the defect's, not the RTL's; the board's race
> (2 / 10 and 0 / 10 fast) is a slot the model lacks, MC-023 item 4. What
> stands: hold >= 9 gives the time-share on 40 / 40 phases of both presets,
> 55 in / 2 out at hold 12 (close_page mixed 62 / 62 against 73 / 121; the
> other OUT, bank_interleave col_major_interleaved_bl4, is OUT at hold 8
> too). The owner's decision is unchanged. Record section 9.

> 2026-11-24 (MC-023 item 4, `char_results/proxy_mc023_refresh_lock_2026-11-24.md`):
> the proxy at the phase-exact default shows the race slot for slot as above
> (`open_page` fast at tREFI 781 of five, `defaults` at 778 of five). Whether a
> run arms it is the refresh's walk through the read turns: stationary on the
> RTL, so a phase always or never reaches the read cap -- the per-run draw. The
> model's walk drifted because its first ACT after a REF was three slots early;
> with the `rfc_block` term (SKU default) the model's `defaults` cell is the
> board's 278 / 278 on 27 / 40 phases. The owner's decision above is unchanged.
