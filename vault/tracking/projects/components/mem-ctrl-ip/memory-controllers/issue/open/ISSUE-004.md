# ISSUE-004: on the mixed window the SKU model's read turns run four times the cap while the RTL's run 255 -- the lane's ACT race on a shared bank after an auto-precharge

> Source: memory-controllers MC-018, 2026-11-17. The granite SKU model reads the
> board's `mixed` union within 9 percent (592 against 543-545 MB/s) but with the
> wrong shape: 296 / 417 write / read where the board measures 272 / 272 after
> MC-017, and 407 direction flips per run where the RTL logs ~2 000 (one per 255
> columns). The model's read turns run ~1 000 columns because the writers'
> ACT never opens a row during a read turn: both directions' heads on the
> shared bank ask for ACT in the same slot after the reader's auto-precharge,
> the lane's rotor sits past the other bank's column winner and wraps to the
> lowest pair, which is the bank-0 READ pair (p = 2 x bank + dir), so the
> reader's own ACT rides every time; with the lane off the model alternates
> fairly (297 / 297, union 594) and the RTL sim measured 264 / 265 lane off.

**Priority:** P3 -- the union is inside the tolerance and the single-direction
cells are within 1 percent; but the turn structure is the term MC-017 fixed in
the RTL, and the model must reproduce it before a `mixed` variant from the
sweep can be trusted.
**Status:** open 2026-11-17
**Owner:** TBD

## The question

Which RTL term lets the waiting direction's ACT win the lane (or the main
slot) after the holder's auto-precharge on a shared bank at the batch cap? The
pick core's lane set has no direction preference (`w2_act_set` is the
candidate set by class, then age -- inert on the SKU, HAS_AGE 0 -- then the
rotor from the held winner's pair + 1), and the main select takes rows first
only when nothing can ride. Candidates: the writer's PRE request on the
auto-precharging row (`bank_row_active` still reads open and the reader's new
head is not a hit, so the courtesy lifts) taking a lane slot and re-timing the
race; the two-cycle stale mask on the reader's just-fired pair; the pop-shadow
record's `behind_same_row` making the reader's AP decision later than the
model's.

## What settles it

`PERF_PICK_PROBE_FLIP` at a cap flip on the granite proxy, lane on, pool 16,
`mixed`: the slot-by-slot lane pick around the holder's AP. The model then
gains the term (`granite_sku_controller.cpp`, the lane pick) and the
`sku_*` mixed column is re-run. Until then the `mixed` and `rw_mix` rows of the
MC-018 sweep carry this as their error bar.
