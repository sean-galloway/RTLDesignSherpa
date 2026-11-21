# ISSUE-006: the SKU model runs `defaults` as plain open page, and on the open-page mixed cell the board's hybrid page predictor never enters the fast mode the model has

> Source: the MC-021 close-out compare read by mode, 2026-11-19
> (`char_results/compare_model_sku_vs_board_sku100s4_s8_modes_2026-11-19.md`,
> the one cell out of 57).

**Priority:** P3 -- the model's default GO phase gives the slow mode, 274 / 274
against the board's 272 / 273, so every single-phase compare of the shipped
SKU is in; the miss is a mode the model CAN show on a preset that never does.
**Status:** CLOSED 2026-11-20 -- resolved into a model term (the RTL's page policy), no RTL change
**Owner:** TBD

## The question

The board's `defaults` preset is the hybrid page predictor; the SKU model has
no term for it and runs the preset as open page (`granite_sku100`, the same
configuration as the `open_page` preset). Through MC-021 that stand-in cost
nothing: every `defaults` cell is within 1.8 percent of the board. The
close-out compare, reading each cell by mode across the board's five windows
runs, found the first place it is visibly wrong:

- `open_page mixed_bl8`: fast 311 / 522 (union 622) on three runs, slow
  272 / 272 (545) on two; the model has both (GO 0 slow 274 / 274, GO 480
  fast 309 / 568, 6 of 40 phases fast). IN by mode.
- `defaults mixed_bl8`: 272 / 273 (545) on all five runs. The model's fast
  phase is a mode the board never showed. OUT.

At the `open_page` proportion, five slow runs of five is about a one-percent
draw, so the predictor is the likely cause: the fast mode is a race on a
zero-column write turn that begins with a PRE closing a row the lane had just
opened (ISSUE-005), and a predictor that closes or keeps rows on its own
history would change which head asks for ACT first at exactly that point.

## What settles it

1. More `defaults` windows runs on the board (the 2026-11-19 bitstream,
   `--profile windows`): ten or more slow runs make the predictor the cause
   beyond the draw; a fast run makes it the draw and closes this with
   no-action (the row is then IN by mode).
2. If the predictor: its rule as a model term in the `GraniteSKU` controller
   (the RTL's hybrid policy, read from the source, not a knob fitted to the
   cell), priced across the SKU's cells -- it must give the slow mode on every
   phase of `defaults mixed_bl8` and move no landed cell.
3. Until then the model carries the stand-in, named in `char_model.py`'s
   docstring, and the compare's one out stands as the record.

## The stand-in has no demand PREs either (MC-019, 2026-11-20)

MC-019 removed the PRE class from the pick core's row lane on the model's
word that a lane carrying ACT or PRE and one carrying ACT only give the same
MB/s on all 29 patterns. The proxy disagreed: on `col_ilv` at the SKU the RTL
issues ~700 demand PREs per run under `defaults` (the hybrid predictor) and
under static `open_page` -- rows the policy left open, closed when the bank's
next row arrives -- and 414-424 of them rode the lane; with the lane ACT-only
each takes a main slot and the read side loses 1.3 percent. The model's
`lane_pre` is 0 on every SKU cell: its open-page stand-in auto-precharges on
drain and never issues a demand PRE, so it priced the PRE path at a command
it does not have. The same missing term as above, with a measured cost now:
the page policy as the RTL has it (the predictor's rule and the static open
policy's no-AP) is what settles both. Until then any lane / PRE question the
model prices is off by the demand PREs it does not issue
(`char_results/rtl_mc019_lane_act_only_2026-11-20.md`, section 4).

## Resolution (2026-11-20): the page policy as the RTL has it

`char_results/model_issue006_page_policy_2026-11-20.md`. The board's
`defaults` is the hybrid (policy_mode 4, tr_init 2: the drain auto-precharge
on a known conflict, on a drained queue only where the bank's history arms
it, else the idle timeout closes the row as the pick's lowest-priority PRE);
its `open_page` is policy_mode 0, the flat close-on-drain the model already
had. Both are in the model now (`page_mode`, `tr_init`; `granite_sku100` the
hybrid, `granite_sku100_open` the flat rule), with the one defect on the way
named in the record (the delayed command view compared against a live image
armed nothing). Result: the by-mode compare is 57 / 0 -- `defaults mixed_bl8`
one mode at every one of 40 GO phases (274 / 274 against the board's
272 / 273 x5), `open_page mixed_bl8` both modes (2 of 40 phases fast),
every `defaults` cell within 1.2 percent; the hybrid issues the demand PREs
and background closes the flat rule never did (4,884 lane PREs on
col_major_interleaved_bl8). The question above is answered as the board
answered it: the predictor, not the draw. No more board runs needed. The
proxy's `TEST_PAGE_POLICY` knob now writes the preset's mode and timeout too.
