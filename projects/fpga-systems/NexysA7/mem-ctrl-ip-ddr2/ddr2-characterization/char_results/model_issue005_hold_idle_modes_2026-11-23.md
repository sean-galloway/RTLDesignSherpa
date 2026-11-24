# ISSUE-005: the mixed cell's two modes are a one-slot race at the batch cap, and the DIR_HOLD_IDLE value decides whether it is a race at all

> memory-controllers ISSUE-005, 2026-11-23. The owner's "work on this". The SKU model
> (`char_model.py`, the GraniteSKU controller at the host default since MC-020:
> phase-exact counters, `ap_seq`, the TIMINGS_RP_AP fields 1 / 2) with its GO swept
> against the refresh phase, 40 phases of one tREFI (39 CK apart), on the
> `mixed_bl8` cell under the board's `open_page` and `defaults` presets; then the
> same sweep with the direction register's knobs moved. The board set is the SKU
> bitstream's (`sku100rpap{,w2,w3}_windows_2026-11-22` and the seven other
> windows runs at the phase-exact counters since 2026-11-21).

> **Correction, same day (memory-controllers MC-023 item 2).** Sections 2, 3,
> 4 and 5a below were measured on a model with a defect: the self-close
> lookahead guard compared `m_clk - fire < close_lag` with `close_lag` 0, true
> while a self-close was still pending, so every ACT request lost its
> lookahead across a pending self-close. Fixed in `granite_sku_controller.cpp`;
> every sweep CSV of this record is now the fixed model's, and section 9 is
> the re-read. What survives: the board's modes (section 1), hold >= 9 giving
> the time-share on 40 / 40 phases of both presets, and its cost on the
> close_page mixed cell. What does not: the model's two-mode race on
> `open_page` and its three modes on `defaults` -- the fixed model is in the
> fast mode on 40 / 40 phases of both -- and the section 3 slot trace, which
> is the defective model's race, not the RTL's.

## 1. The board at the phase-exact counters: ten windows runs

| preset | slow mode (wr / rd) | fast mode | runs |
|---|---|---|---|
| `open_page` | 279.7 / 279.8 x8 | 303.1 / 594 x2 | 10 |
| `defaults` | 276.6 / 276.4 x10 | never | 10 |
| `close_page` | 72.9 / 121 x6 (the field), 60.1 / 65.6 x4 (before it) | one mode each | 10 |

## 2. The model's GO sweep: the pair of modes under `open_page`, three under `defaults`

`model_issue005_go_sweep_granite_sku100_open_2026-11-23.csv`,
`model_issue005_go_sweep_granite_sku100_2026-11-23.csv` (one row per phase, the
`GO offset` in the notes).

| config | mode (wr / rd, union MB/s) | phases of 40 | the board |
|---|---|---|---|
| `granite_sku100_open` | 280 / 280, 560 | 26 | 8 of 10 |
| | 308 / 524, 617 | 14 | 2 of 10 (303 / 594, union 606) |
| `granite_sku100` (`defaults`) | 280 / 280, 560 | 14 | 10 of 10 |
| | 290 / 343, 581 | 22 | never |
| | 305 / 489, 627 | 4 | never |

Under `open_page` the model has the board's pair and a plausible proportion (14
of 40 against 2 of 10; the MC-021 sweep at the margin had 6 of 40 against the
board's 3 of 5). The fast mode's read side is 524 in the model against 594 on
the board: the board's reads run closer to alone than the model's. Under
`defaults` the model is in a mode the board has never shown on 26 of 40 phases
(the 290 / 343 the compare of 2026-11-22 called IN at +5 on the union; it is a
distinct mode, not a tolerance). That is a model-fidelity gap on the shipped
preset and is recorded in section 6; the question this issue asks is the
`open_page` cell's.

## 3. The mechanism, slot by slot (the model at GO 0, the first zero-column turn)

`GRANITE_SKU_DEBUG=12280:12360` on `granite_sku100_open` at GO offset 0 (CK;
pairs are 2 x bank + direction, so p0 / p1 are bank 0's read / write heads, p2 /
p3 bank 1's; the cell's eight walks share two banks, rows apart). The reads hold
the bus, batch 253 .. 255:

| CK | state | what happens |
|---|---|---|
| 12324 | reads, batch 254 | the read head on bank 0 misses (bank 0 holds the WRITE's row, p1COL is a visible hit); its PRE is requested with the ownership term (`DIR_OWNS_ROWS`, the holder's batch not done) |
| 12326 | batch 255 | the 255th column fires; the winner register takes the PRE |
| 12328 | writes, batch 0 | the direction flips on the cap (cause 2) and the read's PRE fires, closing the row the writes were about to use |
| 12330 .. 12334 | idle 1 .. 3 | the write head still reads as a hit (close_lag 2), so it has no request; the read head requests its ACT first (12332) and FIRES it at 12334: bank 0 re-opens with the read's row |
| 12336 .. 12342 | idle 4 .. 7 | the write head is a miss again; its PRE needs the courtesy (granted: the writes own the bus now) and is requested at 12342 |
| 12344 | idle 8 | `hold_idle` = idle < DIR_HOLD_IDLE (8) is FALSE this slot: a read column (bank 1, waiting since the flip) may fire cross-direction and does; the direction flips back to reads (cause 0) with the batch at 0 -- the zero-column turn |

At GO offset 39 the same sequence runs to 12358 (the write's PRE requested at
idle 6, fired at idle 7 = 12360, the idle counter reset) and the writes then
re-ACT and run their 255. The difference between the two phases is ONE slot in
where the write head's miss -> PRE request lands against the idle counter; the
refresh phase shifts the two banks' row-switch cadence against the cap
boundary by that slot. Once the fast pattern forms it sustains itself: the
reads run 255, the cap flips, the writes lose the turn at idle 8, every ~660
CK.

So the "slow attractor" is the design's intended time-share (255 / 255, each
direction at the single-direction ceiling while it holds: 560 is 96 percent
of 583), and the "fast" mode is a read-priority shape the design does not
intend: the writes' turn is taken from them by the hold-idle expiry one slot
before their PRE fires.

## 4. Candidate rules, priced on the 40-phase sweep (both presets)

The knobs that touch the race: `DIR_HOLD_IDLE` (the board builds 8) and
`DIR_OWNS_ROWS` (the ownership term of the PRE courtesy, on). Each run via
`GRANITE_SKU_PARAMS` on the two configs
(`model_issue005_go_sweep_<config>_<knob>_2026-11-23.csv`):

| knob | `open_page`: modes (wr / rd, union) x phases | `defaults`: modes x phases | one mode? |
|---|---|---|---|
| base (hold 8) | 280 / 280, 560 x26; 308 / 524, 617 x14 | 280 / 280 x14; 290 / 343, 581 x22; 305 / 489, 627 x4 | no / no |
| hold 0 (off) | 320 / 656, 639 x34; 356 / 652, 711 x4; 401 / 266, 532 x2 | 39x / 270, 541 x40 | no / yes (slow-ish) |
| hold 4 | 48x / 296, 592 x40 | 319 / 632..656, 638 x36; 518 / 297 x2; 355 / 640 x2 | yes (write-first) / no |
| hold 6 | 286 / 295, 566 x40 | 313 / 630, 627 x24; 446 / 29x, 58x x14; 315 / 600 x2 | yes (+1) / no |
| **hold 12** | **280 / 280, 560 x40** | **280 / 280, 560 x40** | **yes / yes** |
| hold 16 | 280 / 280, 560 x40 | 280 / 280, 560 x40 | yes / yes |
| owns-rows off | 195 / 196, 391 x40 | 195 / 196, 391 x40 | yes, and -30 percent |

No value gives the fast mode on every phase of both presets: the read-first
shape appears (hold 0 on `open_page`, hold 4 / 6 on `defaults`) but always
with phases in another mode, because the same one-slot race moves rather than
closes. What DOES close it is a hold-idle longer than the write head's miss ->
PRE -> fire chain: at 12 (and 16) both presets land in the time-share mode on
all 40 phases, the board's `defaults` behaviour (10 of 10) and the board's
`open_page` majority (8 of 10). The cost against the base is the fast mode's
union on the phases that had it: 617 -> 560 on `open_page` (-9 percent on 14
of 40 phases, 0 on 26), 627 / 581 -> 560 on `defaults` (where the board never
showed those modes). What it buys is a deterministic cell.

## 5. The landed cells under hold 12 (and 9, 10)

Hold 9 and hold 10 give the same 40 / 40 time-share mode as 12 on both
presets (`..._hold9_`, `..._hold10_` CSVs), so the smallest value that closes
the race is 9. The full `all` suite (every + windows) on the four SKU configs
with `dir_hold_idle=12`, against the SKU bitstream's board set
(`board-compare --granite sku100rpap_2026-11-22 --board-also` the w2 / w3
windows runs): **55 in / 2 out**, and the two OUT cells are the field's two
gains:

| preset | cell | board | model, hold 12 | model, hold 8 (2026-11-22 CSV) | hold 9 / 10 |
|---|---|---|---|---|---|
| close_page | mixed_bl8 | 73 / 121 (union 146) x3 | 61 / 61 (122), -16 percent | 73 / 121 | 62.5 / 63.7 at 9, 61 / 61 at 10 |
| bank_interleave | col_major_bl4 | 445 / 516 | 446 / 446, -13.6 on the read | 446 / 520 in the CSV; **446 / 446 from the committed model** (section 5a) | 446 / 446 |

Everything else is within one percent of the hold-8 model (60 cells, 11
directions moved, nine of them the two mixed cells above and the open /
defaults mixed cells' fast phases). So the deterministic time-share costs
the close-page mixed cell its read-first shape (the board's 73 / 121 is the
same read-first shape the open_page fast mode has, and the board takes it 6
of 6 with the field): a longer hold keeps the writes on the bus through the
cap turns that cell flips at 16. The candidate is priced and not free.

### 5a. A note on the 2026-11-22 model CSVs

Re-running the committed model today on `granite_sku100_bi col_major_bl4`
gives 446 / 446 with or without the TIMINGS_RP_AP field, where the
`model_ramulator2_ddr2_granite_sku100_bi_rpap_2026-11-22.csv` row says 446 /
520 (the board: 442 -> 516 with the field). That CSV was written at 14:33 on
2026-11-22, before the `ap_seq` term was finished (16:44); the finished term
holds this cell's read ACT one slot past tRC (a seven-cycle rotation of the
four banks for six) and the `_close_` CSV's mixed row (73 / 121) is 73 / 117
from the committed model. The term's `ap_seq=false` variant gives the CSV's
520. So the MC-020 record's "the model priced 446 / 520 and the board
delivered 442 / 516" is right about the board and wrong about the committed
model; the record carries an addendum and the fix is memory-controllers
MC-023. Nothing in this record depends on that cell except the hold-12 row
above, which is 446 either way.

## 6. Model fidelity on `defaults`

The board's `defaults` mixed cell is 276.6 / 276.4 on every one of ten runs;
the model at hold 8 lands there on 14 of 40 phases and in two other modes on
26. With hold 12 the model is there on 40 of 40. Read with section 3, the
RTL's write head reaches its PRE fire within the eight idle slots on every
phase under the hybrid policy, where the model's chain takes one slot longer
on 26 of 40. The model term is the slot count of the miss -> PRE -> fire chain
under `page_mode` 4 (the hybrid's drain gate on the PRE request), not
measured on the proxy yet; under `page_mode` 0 (the `open_page` preset) the
chain's length matches the board's pair and proportion. Until it is measured
the `defaults` mixed cell's compare is read by mode and the model's 290 / 343
is OUT (a mode the board never shows), not IN at +5.

A second fidelity item from the same sweep: the model's fast mode on
`open_page` reads at 524 where the board's reads at 594 -- the board's
readers run closer to alone during a zero-column turn than the model's,
which lets some write columns through (the model's 309 writes against the
board's 303 say the same). Both items go to MC-023.

## 7. What this leaves for the owner

The issue's question was whether the pick core should take the fast mode
deterministically, and whether its shape is acceptable. The sweep says the
fast mode cannot be made deterministic by the direction register's knobs; it
is a race the design loses one slot at a time. The deterministic choice on
offer is the time-share, by building `GRANITE_SCHED_DIR_HOLD_IDLE` 12 instead
of 8 (a package parameter, `granite_pkg.sv`; a bitstream and the proxy's
`TEST_DIR_HOLD_IDLE` knob -- the proxy has the batch cap's `TEST_DIR_BATCH_MAX`
and would need the same plumbing for the hold), with the landed-cell cost of
section 5; or a recorded no-action, since the shipped preset is one mode on
the board already and the race is the `open_page` preset's. A read-priority
design that makes the fast shape the rule (the writes drained only when no
read column is ready, with a starvation bound) is a different direction
register, not a knob, and is not priced here.

## 8. Record

- Model sweeps: `model_issue005_go_sweep_granite_sku100{,_open}_2026-11-23.csv`
  (base), `..._{hold0,hold4,hold6,hold12,hold16,noown}_2026-11-23.csv`; 40 rows
  each, `GO offset` in the notes. Model runs at 4 s per phase; the debug trace of
  section 3 is `GRANITE_SKU_DEBUG=12280:12360` on `granite_sku100_open`, GO 0 and 39.
- Board: `char_granite_sku100{px,pxd,pxdw2,pxdw3,rpapA,rpapAw2,rpapAw3,rpap,rpapw2,rpapw3}_windows_2026-11-2[12].csv`.
- No RTL, model-term or formal change in this record; `char_model.py` unchanged
  (the knobs existed; `GRANITE_SKU_PARAMS` carried them).

## 9. Re-read on the fixed model (MC-023 item 2)

The guard fix restores the 2026-11-22 model CSVs to the cycle (the `_rpap_`
and `_rps_` sets, 120 of 120 cells), so the MC-020 compares stand as
written. The GO sweeps of this record, re-run (the CSVs above are these):

| knob | `open_page` modes (wr / rd) x phases | `defaults` modes x phases |
|---|---|---|
| base (hold 8) | 308 / 517 .. 525 x40 | 309 / 560 .. 571 x38; 340 / 562 x2 |
| hold 0 | 320 / 656 x32; 356 / 652 .. 656 x6; 401 / 266 x2 | 394 .. 400 / 266 .. 269 x40 |
| hold 4 | 456 .. 461 / 292 x35; 483 / 289 .. 293 x5 | 319 / 632 .. 656 x34; 519 / 294 x2; 355 / 639 .. 645 x4 |
| hold 6 | 314 .. 316 / 579 .. 600 x38; 347 / 590 x2 | 313 / 630 x22; 348 / 630 x2; 442 .. 448 / 289 x16 |
| hold 9 / 10 / 12 / 16 | 281 / 281 x40 | 280 .. 281 / 281 x40 |
| owns-rows off | 195 / 197 x40 | 195 / 197 x40 |

So the fixed model takes the read-first fast mode on every phase of both
presets, where the board takes it on 2 of 10 `open_page` runs and 0 of 10
`defaults` runs. The model is now one-sided on the race the board shows,
which makes the fidelity gap of section 6 apply to both presets: on the
RTL the write head's miss -> PRE -> fire chain wins the slot against the
hold-idle expiry most of the time, and on the model it never does. The
defect had made that chain look closer to the RTL's by delaying the reads'
re-ACT after the drain self-close, the record-path term of MC-023 item 1.

The `ap_close_rec` probe (heads of the closed row requested off the
record path) does NOT recover it on the fixed model: the mixed cells are
unmoved (308 / 521, 309 / 562 across 40 phases), and the probe over-prices
every close_page read side by 34 .. 50 percent (40 in / 17 out against the
SKU board set). Its 2026-11-23 "lands all four" figures were the defective
model's. Item 1 needs the proxy measurement MC-023 names before it is a term.

Hold 12, full `all` suite on the four configs against the SKU board set:
**55 in / 2 out** -- close_page mixed_bl8 62 / 62 against 73 / 121 (-15 on
the union), and bank_interleave col_major_interleaved_bl4 355 / 402
against 356 / 361, which is OUT at hold 8 as well (MC-023 item 1). The
bank_interleave col_major_bl4 OUT of section 5 was the defect (446 / 520
on the fixed model, the board 442 -> 516).

Section 7's decision is unchanged: hold >= 9 is the only knob value that
makes the cell one mode on every phase, at the close_page mixed cell's
read-first shape; or a recorded no-action; or a read-priority design.
ISSUE-007 is unchanged: 584.6 on all 120 directions of the fixed model.
