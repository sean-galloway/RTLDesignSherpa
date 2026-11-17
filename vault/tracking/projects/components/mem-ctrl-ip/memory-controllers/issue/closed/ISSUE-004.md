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
**Status:** CLOSED 2026-11-17 -- resolved into a model fix (three admission terms), no RTL change
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

## Resolution (2026-11-17)

The probe (`PERF_PICK_PROBE_FLIP=4`, with the decode's class, the bank
timers, the head records and the store's `r_rd_valid` / `r_wr_valid` and
per-bank counts added) answered the question in the store, not in the pick:
the RTL's rotor rule is the one the model copied, but at the holder's
auto-precharge the holder's next burst on the shared bank is NOT in the store.
`BANK_CAP_MIXED` is checked at every push with in-order chopping, so each
direction holds six beats and the next burst's first beat lands as a
schedulable head five cycles after the pop that freed its slot; the waiting
direction's ACT rides the lane unopposed, its row is opened, the holder's
next burst closes it, and the write head's three open cycles a period are
what the cap flip reads. The model held both banks' next bursts (the cap once
per burst, 13 per bank; a beat a head the slot it was accepted) so the
holder's ACT always had the lower pair.

Model terms added (`granite_sku_controller.cpp`, each a knob with the MC-018
form a `sku_*` variant): the cap at every push (`cap_per_beat`), a 4-slot
admission stage from acceptance to head (`admit_lag`), the decode's request
on the bank's timers with the rank-level terms holding the fire
(`req_bank_timing`); the frontend's split mode re-stamps each direction's
ticks with its own beat order. `mixed`: 286 / 286 (union 573, +5.5 percent on
the board's 543, inside the 10 percent tolerance), 255 flips all at the cap,
turns 319 / 380 slots against the RTL's 313 / 432; every single-direction SKU
cell unchanged within 0.4 percent. The write turn's missing 52 slots (the
write-data fill and commit back-pressure, the decode -> pick -> fire stages)
are the `mixed` error bar now. The two presets already out (ISSUE-002 / 003)
moved +25 percent further from the board on their ACT-bound rows; they carry
the numbers. Write-up: `char_results/model_issue004_admission_lag_2026-11-17.md`;
handbook: `vault/handbook/dv/dram-cycle-model.md` ("The admission pipeline
decides who gets the ACT").
