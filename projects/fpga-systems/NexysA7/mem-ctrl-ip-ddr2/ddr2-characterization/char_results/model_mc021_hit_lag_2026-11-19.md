# The record's hit lag: the model's bl4 attractor explained (memory-controllers MC-021 step 4, 2026-11-19)

**Question (MC-021 "What next" item 1 after step 3):** the model sat 55 in / 2
out against the board, the two out being the `bank_interleave col_major` bl4
read sides at +11 percent (389 against 351; `col_major_interleaved_bl4` 281
against 253). Step 3 had shown the same pick rules settling into different
fixed points: the RTL a steady 11-13-cycle read pattern with one 3-cycle ACT
gap, the model an aligned 8-cycle one. The item said: replay the first cycles
of the bl4 read phase on the proxy beside the model's slot debug and find
which rule's timing sends the RTL into the slower pattern.

**Answer:** not a rule, a register. The head record's row-hit flag is
classified in the storage plane against the bank timers' REGISTERED row image
("one cycle stale by contract", `mc_bank_head_records`) and registered into the
record, and the pick registers the decode once more: a bank's column request
is visible three cycles after its ACT (72 of 72 in the probe). The model read
the hit live and showed the request at ACT + 2. The hinted column fires at
ACT + 2 in both, so the term is invisible on the common path; it binds when a
hold discards the hint, and there the model's column fired at ACT + 3 where
the RTL's fires at ACT + 5 or + 7 -- and under a four-bank rotation at the tRRD
floor (8 cycles per round against tRC 7, one cycle of slack) a column at
ACT + 5 pushes that bank's next ACT past its slot. With the term (`hit_lag` 2,
the RTL's value) the model reproduces the RTL's hop distributions, not just
its number: `col_major_bl4` 258 / 355 against the board's 258 / 351,
`col_major_interleaved_bl4` 247 / 246 against 242 / 253. Compare 55 / 2 ->
**56 / 1**; the SKU's 30 cells moved 0.7 percent at most (`mixed_bl8` 2.1
percent, toward the board). The one cell out is new and in another regime:
`close_page col_major_interleaved_bl16`, read side -15.2 against 15, where the
proxy equals the board (section 4). The RTL question the mechanism raises is
priced in section 5.

## 1. The replay

The proxy's pick probe anchored on the second direction flip (the write pass
to the read pass; `PERF_PICK_PROBE_FLIP=2`, 160 cycles). The absolute cycle is
not stable between runs -- the read phase began at 114329 in one run and 113428
in another with the same shape -- so a fixed-cycle window missed; the flip count
does not move. The model's read pass dumped from its first slot
(`GRANITE_SKU_DEBUG=0:400`) and in steady state (`20000:20400`).

One stretch of the RTL's steady pattern, read pass, pairs p0 / p2 / p4 / p6 =
banks 0..3, `win` the main winner register (F fire, H hold, s stale: the class
no longer applies), `lane` the row lane's register (F fire, H hold, c clash
with the main winner's bank), `pick` the select's pair and source (`L` = the
lane's load), `hint` the one-cycle next-op hint:

```
cyc    | req (pair,cls; * stale)      | win       | lane      | pick         | hint
114360 | p0COL p4row* p6row           | p4ACT:F   | p2ACT:t   | p0/cdir L6   | -
114361 | p0COL* p2COL p4row p6row*    | p0COL:F   | p6ACT:H   | p4/hint L4   | p4COLok
114362 | p0COL p2COL p6row*           | p4COL:F   | p6ACT:F   | p0/cdir      | -        <- the leftover of 361's column wins the select over p2's real column (rotor starts past p4)
114363 | p0row* p2COL p4COL p6row*    | p0COL:s   | -         | p6/hint      | p6COLok  <- slot wasted on the stale pick; p0's fresh ACT request masked from the lane (p0row*)
114364 | p0row p2COL                  | p6COL:F   | -         | p2/cdir L0   | -        <- no lane ACT beside this column (nothing loaded at 363)
114365 | p0row* p2COL* p6COL          | p2COL:F   | p0ACT:F   | p6/cdir      | -        <- p2's column at ACT + 7 (its ACT was 358); the leftover of 364 picked again
114366 | p0row* p2COL p4row           | p6COL:s   | -         | p0/hint L4   | p0COLok
114367 | p2row p4row*                 | p0COL:F   | p4ACT:F   | p2/row L2    | -        <- no column live: the main takes p2's ACT as a row pick (the lane loads it too)
114368 | p0COL p2row* p4row* p6row    | p2ACT:H   | p2ACT:c   | p4/hint L6   | p4COLok  <- the main holds the ACT under tRRD; p4's hint (the lane ACT of 367) is computed and DISCARDED
114369 | p2row* p6row*                | p2ACT:F   | p6ACT:H   | -            | -
114370 | p2row p4COL p6row            | -         | p6ACT:H   | p2/hint L6   | p2COLok  <- p4's column request appears at ACT + 3, loses the select to the main ACT's own hint
114371 | p0row p4COL p6row*           | p2COL:F   | p6ACT:F   | p4/cdir L0   | -
114372 | p0row* p2COL p4COL* p6row*   | p4COL:F   | p0ACT:H   | p6/hint      | p6COLok  <- p4's column at ACT + 5: RDA at +5 puts its next ACT at +8, past the rotation's slot
```

The model with the hit read live runs the same rules through its first forty
slots (holds, discarded hints, stale leftover picks) and then settles into the
aligned pattern: every fire slot a column plus a lane ACT, every hint taken,
every column at ACT + 2, no main ACT at all (50 of 50 ACTs on the lane in the
steady window). The RTL never gets there, and the reason is one hop.

## 2. The hops, RTL against model

Counts over the RTL probe's 160 cycles and 200-slot model windows (steady
state for the model; the RTL's pattern is steady from the phase's first
cycles). The lane's ACT is timed at its slot (step 3).

| hop (MC cycles) | RTL (proxy probe) | model, hit read live (step 3) | model, `hit_lag` 2 (step 4) |
|---|---|---|---|
| ACT -> column REQUEST visible | 3: 72 of 72 | 2: 97 of 97 | 3: 82 of 82 |
| ACT -> column fire | 2: 54, 5: 13, 7: 5 | 2: 49 of 49 | 2: 58, 5: 14, 7: 6 |
| same-bank ACT -> ACT | 7: 13, 8: 19, 9: 25, 11: 12 | 8: 46 of 46 | 7: 14, 8: 20, 9: 28, 11: 14 |
| column -> the bank's next ACT | 4: 12, 5: 13, 6: 26, 7: 20 | 6: 47 of 47 | 4: 13, 5: 14, 6: 28, 7: 22 |
| ACTs lane / main | 46 / 27 | 50 / 0 | 51 / 33 |
| main slots fire / hold / stale / empty | 101 / 19 / 33 / 7 | 50 / 0 / 0 / 50 | 112 / 39 / 38 / 11 |
| cycles per beat (read) | 2.17 | 2.00 | 2.17 (354.9 MB/s; board 351) |

The one row that separated the two before the term is the first: the column
request's visibility. Everything below it follows. The RTL's distributions
and the step-4 model's are the same shape in every row.

The mechanism, in the order the probe shows it:

1. A column fires with auto-precharge. The cycle after, its pair's request
   register still shows a COLUMN (the record lags the backend by one cycle)
   and is live again (the pick's stale mask lasts one cycle; the fire masks a
   pair only when its queue emptied). The rotor starts just past the fired
   pair, so this leftover beats the bank whose column is really ready.
2. The leftover is loaded, found stale at the fire stage (a wasted slot), and
   its pick sets the pair's stale bit for that cycle -- masking the bank's
   FRESH ACT request from the lane pick for the one cycle the lane could have
   taken it beside the next column.
3. With no live column, the select falls through to a row pick: an ACT lands
   in the MAIN winner register and holds through the tRRD wait. The hold wins
   the register's D input, so the hint raised by the lane's ACT in the same
   cycle is discarded.
4. The column whose hint was discarded is found by the decode at ACT + 3 (the
   record path), loses the next select to the main ACT's own hint, and fires
   at ACT + 5 (or + 7). Its auto-precharge then closes the bank at ACT + 8,
   past the 8-cycle rotation slot, and the ACT stream shows a 3-cycle gap.
5. The gap shifts the phase between the column stream and the ACT stream so
   that step 1 recurs: the 11-13-cycle pattern is the fixed point.

With the hit read live, step 4 fires the column at ACT + 3, its close lands at
ACT + 7 = tRC, the bank keeps its slot, and the pattern relaxes to the floor.

## 3. The term

RTL: `mc_bank_head_records` classifies each entry's hit against
`bank_row_active_i` / `bank_open_row_i`, "the scheduler's registered row image
(bank timers' flops) ... one cycle stale by contract", into records that are
"REGISTERED snapshots, one cycle behind the CAM state" (`mc_storage_plane`);
`mc_bank_pick`'s decode registers the class once more. ACT at c, row image at
c + 1, record hit at c + 2, request register at c + 3. The ACT class after a
pop takes the other path (the bank state with the lookahead, visible at
ready - 1, measured in step 3 at 39 of 39), which is why one decode has two
latencies and why measuring one of them was not measuring the other.

Model (`granite_sku_controller.cpp`): `hit_lag` (default 2 slots) -- a bank's
heads are classified as row hits by the decode only `hit_lag` slots after the
bank's last ACT (`m_bank_act_clk`, stamped by both the main and the lane ACT
at the slot tick; `hit_visible()` in the decode's column branch). The hint and
the fire stage read the live head as before, so the hinted column still fires
at ACT + 2. `hit_lag` 1 is the step-3 model (`sku_hitlag1` variant). Tests:
`test_hit_lag_is_the_record_path_not_the_live_row_image` (the read side of the
bl4 cell drops to 0.85-0.97 of the live-read value), the shipped-point test
carries the default; 37 / 37, vendor suites 217 / 217.

Against the board set `sku100bug004b_2026-11-18`
(`compare_model_sku_vs_board_sku100bug004b_hitlag_2026-11-19.md`): 55 / 2 ->
56 / 1. Every cell whose model value moved by more than rounding:

| preset | cell | board | model step 3 | model step 4 |
|---|---|---|---|---|
| bank_interleave | col_major_bl4 | 258 / 351 | 283 / 389 (OUT) | 258 / 355 (+0.1 / +1.1) |
| bank_interleave | col_major_interleaved_bl4 | 242 / 253 | 246 / 281 (OUT) | 247 / 246 (+2.1 / -2.6) |
| bank_interleave | col_major bl8 / bl16, row_major, interleaved bl8 / bl16 | 387 / 387 | 389 / 389 | 388 / 388-389 |
| defaults, open_page | col_major_interleaved bl4 / bl8 / bl16, row_thrash, random | 762-772 | 777 / 779-780 | 775 / 775-779 |
| defaults | mixed_bl8 (union) | 537 | 580 (+8.0) | 567 (+5.6) |
| open_page | mixed_bl8 (union) | 545 | 580 (+6.4) | 567 (+4.1) |
| close_page | col_major_interleaved_bl4 | 379 / 387 | 389 / 389 | 388 / 388 |
| close_page | col_major_interleaved_bl8 | 251 / 328 | 275 / 309 | 284 / 302 (+13.4 / -7.8) |
| close_page | col_major_interleaved_bl16 | 171 / 240 | 184 / 240 | 191 / 204 (+11.7 / -15.2, OUT) |
| close_page | row_thrash_bl8 | 246 / 251 | 249 / 271 | 243 / 266 |
| close_page | random_bl8 | 204 / 234 | 217 / 244 | 216 / 232 |

The SKU's 30 cells (`defaults`, `open_page`): the row-hit families did not
move; the interleaved and random cells moved 0.2-0.7 percent toward the
board; `mixed_bl8` moved 2.1 percent toward the board and is still 5.6 over.

## 4. The cell that went out: close_page col_major_interleaved_bl16

The proxy on the close_page preset (page policy 2, the default map), `col_ilv`
at AxLEN 16 and 8, one injector, pool 16, 2048 transactions per pass
(`scratchpad/mc021/dram_close_ilv_bl{16,8}.json`): from the DRAM trace's
column spans, bl16 writes 4.68 cycles per beat and reads 3.45 (171 / 232 MB/s
against the board's 171 / 240), bl8 3.22 / 2.50 (248 / 320 against 251 / 328).
The proxy is the board on these cells; the model is not, on either side.

Its hop signature is not the bl4 one. Reads: ACT -> column 2 for 87 percent
(5: 10, 6: 3), the auto-precharging column -> the bank's next ACT 7 for 70
percent (the same-row head after the auto-precharge: the walk steps the eight
banks and comes back to the same row), same-bank ACT -> ACT 9 for 68 percent.
Writes: ACT -> column 2 and 5 half each, column -> ACT 8 / 9 / 10, same-bank
ACT -> ACT 10-15. The RTL's reads keep their hint on this cell where its
writes pay the record path on every second column.

The model on the same cell (slot debug, both passes) runs a different regime:
one or two heads in flight most of the time, half the main slots empty, 134 of
152 read ACTs from the main register with a hold, and 68 of 148 read columns
at ACT + 5 (the discarded-hint path the hit lag now prices); its same-row
auto-precharge -> ACT hop lands at 5 / 6 and 8 / 9 where the RTL's lands at 7.
This is the host-path-bound regime the close_page tolerance (15) was widened
for: an AxLEN-16 burst against a 16-entry pool, admission one beat per tick.
The read side was on the board before the term only because the live hit hid
the pipeline this cell exposes; the write side was already +7.6. The cell is
MC-021's next item: the pick probe on the proxy's read pass beside the model's
slot debug, with the three signatures above as the match.

## 5. What it says about the RTL, and the price of the fix

The loss is the leftover pick: a column request that the pick's own stale
mask has already released, one cycle after the pair's column fired with
auto-precharge, winning the select because the rotor starts past the fired
pair. It costs the slot it is loaded into, and it masks the pair's fresh ACT
request from the lane for the one cycle that lane could have used. The RTL
masks a fired pair only when its queue emptied (`w_col_fire_now &&
behind_empty`); a column that fired with auto-precharge cannot be followed by
a column from the same pair for at least t_rtp + t_rp, so masking that pair
for the cycle after its fire cannot lose anything. Priced in the model as
`ap_fire_stale` (one term in the stale mask's fire case, off by default;
`sku_apfirestale` variant), `hit_lag` 2 throughout:

| preset | cell | RTL as it is | masked | delta | board |
|---|---|---|---|---|---|
| bank_interleave | col_major_bl4 | 258.5 / 354.9 | 283.1 / 389.2 | +9.5 / +9.7 | 258 / 351 |
| bank_interleave | col_major_interleaved_bl4 | 246.8 / 246.2 | 246.2 / 321.5 | -0.3 / +30.6 | 242 / 253 |
| bank_interleave | col_major_bl8 / bl16 | 388 / 388 | 389 / 389 | +0.2 | 387 / 387 |
| close_page | col_major_interleaved_bl8 | 284 / 302 | 287 / 334 | +1.0 / +10.4 | 251 / 328 |
| close_page | col_major_interleaved_bl16 | 191 / 204 | 208 / 239 | +8.6 / +17.2 | 171 / 240 |
| close_page | random_bl8 | 216 / 232 | 218 / 258 | +1.1 / +11.4 | 204 / 234 |
| close_page | mixed_bl8 | 58 / 74 | 58 / 76 | +0.8 / +2.2 | 56 / 56 |
| SKU (defaults) | col_major bl4 / bl8, incremental, random | unchanged | unchanged | 0.0 (random read +0.7) | |
| SKU (defaults) | mixed_bl8 | 284 / 284 | 277 / 277 | -2.4 | 269 / 269 |

The four-bank close-page cells recover the whole 10 percent (to the tRRD
floor the step-3 model predicted), the interleaved read sides a quarter to a
third, the SKU nothing it would miss. The RTL change is one AND term in
`r_self_stale`'s fire case (`w_col_fire_now && (behind_empty || cmd_ap_o)`),
in the fire cone's D inputs where the stale mask already is. It is MC-021's
RTL question in its measured shape, to be run under `TEST_DUAL` both ways,
through the formal tasks under `formal/mc_common/mc_bank_pick`, and against
the 100 MHz cone before it is believed.

## Files

- `granite_sku_controller.cpp` (overlay and the vendor copy): `hit_lag`,
  `hit_visible()`, `m_bank_act_clk`; `ap_fire_stale`.
- `bin/char_model.py`: `ModelConfig.hit_lag` / `ap_fire_stale`, the variants
  `sku_hitlag1`, `sku_apfirestale`.
- `tests/test_char_model.py`: the hit-lag test, the shipped-point defaults.
- `model_ramulator2_ddr2_granite_sku100{,_bi,_close}_hitlag_2026-11-19.csv`
  and the compare above.
- Scratchpad `mc021/`: `pick_bl4_start.json` (the probe), `replay_table.py`,
  `model_table.py`, `hops_rtl.py`, `hops_model.py`, the model dumps
  `model_bi_bl4_hl2_{start,mid}.out`, `model_close_ilv16_dbg.out`, the proxy
  traces `dram_close_ilv_bl{16,8}.json`, `abl4.py`, `price.py`.
