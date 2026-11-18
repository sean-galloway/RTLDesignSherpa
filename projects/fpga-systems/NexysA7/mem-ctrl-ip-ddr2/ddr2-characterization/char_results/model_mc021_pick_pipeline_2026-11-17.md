# MC-021: the pick pipeline in the SKU model (2026-11-17)

The granite SKU's Ramulator model now carries `mc_bank_pick`'s three stages --
the decode's request register, the winner register with its hold, speculation
and fresh pick, the self-stale mask, the next-op hint, the row lane as a second
winner register, and the registered rank ok of `mc_global_timers` -- instead
of firing a selected command in the slot it is selected. The two-cycle hop
MC-021 was filed on is those registers; a lag term in their place reproduced
one probe window and missed the distribution.

**One setting.** `admit_lag` 3 (push -> bank FIFO -> head record; the fourth
cycle ISSUE-004 measured to the request is now the pipeline's own register),
`pick_la` 2 (the lookahead's and the hint's reach, LA), `rank_ok_lag` 1 (the
ACT's tRRD / tFAW ok registered), the two RTL questions off. Against the board
(granite sku100def 2026-11-16, 57 cells):

| preset | before (8d591fcd9) | now | mean abs delta | worst cell |
|---|---|---|---|---|
| the SKU (`defaults` + `open_page`, 30 cells) | 30 / 30 | **30 / 30** | 0.8 % | random_bl8 +2.0 % |
| `close_page` (15) | 1 / 15 | **14 / 15** | 5.0 % | col_major_interleaved_bl16 -26.9 % |
| `bank_interleave` (12) | 0 / 12 | 1 / 12 | 14.9 % | col_major_bl4 +23.4 % |

The SKU's `col_major` cells, which the first pipeline draft broke by 8-20
percent, sit at +0.1 / +0.6 / +0.1 (283 / 390 against the board's 283 / 389 on
bl4) once the decode arms the ACT after a drain close the way the RTL does
(section 3). `mixed_bl8` moved from +5.5 to +1.7 percent. `close_page` is on
the board on every single-bank cell (82 / 92 -> 83 / 93; the rows 78 / 87 ->
78 / 87). `bank_interleave` is the residual: -15 percent on the row-hit cells,
with the mechanism named in section 5 and not tuned away.

## 1. Why the lag term was wrong

The first draft carried the measurement as terms: `hop_lag` (an un-hinted
command fires two slots after its timer), `rank_ok_lag`, `col_row_lag` (two
empty slots after a column before a row command), `hold_winner`. On the
eight-bank close-page chain it gave a rigid eight-slot period per two beats
(195 MB/s against the board's 234); the RTL's probe shows six-, seven- and
eight-slot periods (ACT -> ACT gaps 3 in 80 percent, 4 and 5 for the rest) and
the two patterns MC-021 recorded (ACT -> COL 2 in 60 percent, 4 in 40) are the
pipeline's own race: whether the winner register at the ACT's fire cycle
already holds the next ACT (which then blocks the hinted column) or is empty
(the hint takes it). No lag reproduces a race; the registers do.

The RTL probe (`PERF_PICK_PROBE`, the same bi_close run as
`model_knob_grid_2026-11-17.md` section 3, 64 cycles from 60000) read cycle
by cycle against `mc_bank_pick.sv`:

```
cyc lwr  r_req (pairs)   self_stale   sel   pick | winner  cls tim FIRE hold | hint   | lane  ride anycol
  1  1   p3C p5 p7 p9..  p5 p9        CDIR  3    |  5ACT   1   1   1    0   |   -    |  7ACT  1    1
  2  1   p3C p5..p15     p7           HINT  5    |  3COL   1   1   1    0   |  5COL  |  7ACT  1    1
  3  0   p3C p7..p15     p5 p7        CDIR  3    |  5COL   1   1   1    0   |   -    |  7ACT  1    1
  4  0   p5C p7..p15     p3 p5 p7     ROW   9    |  3COL   1   0   0    0   |   -    |  7ACT  1    0
  5  0   p7..p15         p9           ROW  11    |  9ACT   1   1   1    0   |   -    |  7ACT  1    0
  6  1   p7..p15         p11          HINT  9    | 11ACT   1   0   0    1   |  9COL  |  7ACT  1    0
  7  1   p7 p11..p15     p11 p13      ROW  15    | 11ACT   1   0   0    1   |   -    |  7ACT  1    0
  8  1   p1 p7 p9C..     p11 p15      CDIR  9    | 11ACT   1   1   1    0   |   -    |  7ACT  1    1
  9  1   p1 p3 p7 p9C..  p7           HINT 11    |  9COL   1   1   1    0   | 11COL  |  7ACT  1    1
 10  0   p1 p3 p7 p9C..  p7 p11       CDIR  9    | 11COL   1   1   1    0   |   -    |  7ACT  1    1
 11  0   ..p11C..        p7 p9        CDIR 11    |  9COL   1   0   0    0   |   -    |  7ACT  1    1
 12  0   ..              p7 p11       ROW  13    | 11COL   1   0   0    0   |   -    |  7ACT  1    0
 13  0   ..              p13          ROW  15    | 13ACT   1   1   1    0   |   -    |  7ACT  1    0
```

Cycle 3 -> 4 -> 5 wastes one slot (the stale pair 3 re-picked at 3 fails at
4; at 4 the stale pair 5 is masked and the row class is taken); 10 -> 13
wastes two (pairs 9 and 11 both re-picked, neither masked). The mask is the
difference: it fires on a pair whose fired column had NOTHING FILLED behind it
(`behind_empty`, mc_bank_fifo_store: "the next position is not filled") or
whose re-picked candidate, read through the pop shadow, has no same-row entry
behind. Whether a bank holds one or two schedulable entries at the fire decides
the waste, slot by slot.

## 2. What the model carries now (`granite_sku_controller.cpp`)

Per main slot, in the RTL's order and from the RTL's registers:

- **Decode -> request register.** Each pair's head is classified against the
  live bank state (row hit -> COL; open row + miss -> PRE with the DIR_OWNS_ROWS
  courtesy; closed -> ACT) and its BANK timer with the lookahead `pick_la`
  (requested when the timer opens within LA slots, `safe_*_la`); the result is
  read by the select NEXT slot. Rank-level terms are the fire's
  (`req_bank_timing`, ISSUE-004).
- **Select -> winner register.** From the request registers less the
  self-stale mask; the rotor from the pair past the effective winner; after a
  row command columns first, after a column rows first, a rideable row
  counting as "after a row" (`w2_ride`); the hint, the holding direction's
  columns, the other direction's under `xdir_ok`, the hint again, the preferred
  direction's rows -- the RTL's two branches verbatim. The register loads the
  HELD winner (valid, class applies, bank opens within LA, did not fire; a
  column of the other direction yields once the holder has a column pending),
  else the short-hop speculation (t < LA on the same pair), else the pick.
- **Fire.** The winner against the LIVE head (the class must still apply: a
  stale pick costs the slot and is released) and the live timers; an ACT's
  tRRD / tFAW as they stood `rank_ok_lag` slots earlier. A fire raises the hint
  for its pair (ACT -> COL at tRCD, PRE -> ACT at tRP, a last-of-row column
  without auto-precharge -> PRE at tWR / tRTP; t <= LA, t > LA - 1).
- **The self-stale mask** for the next slot: the held / speculated / picked
  pair when its command is a row command or a column with no same-row entry
  behind, the fired column's pair when nothing is behind it, the lane's pair
  while it holds with a column pending somewhere, the slot after its load and
  the slot after its fire.
- **The lane** as a second winner register picked from the same request
  registers (a row request on a bank with no column request, ACT before PRE,
  the rotor), fired beside a main-slot column only, never to the main winner's
  bank, with the same registered rank ok; it holds while its class applies and
  its bank opens within LA.
- **The direction register** in the RTL's register form: the leftover rule,
  the follow, the drain (no column pending in the held direction, one ready in
  the other, not inside the idle hold, no row request or row winner of the
  held direction), the cap.

Two measured exceptions are rules, not terms:

- **The ACT after an auto-precharge.** A head that MISSES the closing row goes
  down the decode's miss branch, whose act lookahead carries the self-close
  extrapolation (`mc_bank_timer` LA_AP, on for the bank-pick core): armed up
  to LA ahead. That is the SKU's drain close, and the `col_major` cells need
  it (section 3). A head that HITS the closing row -- close page, the next
  column of the same row -- is classified as a column, blocked until the row
  image closes, and its ACT is requested only once the timer is open: the
  measured two-slot hop (one bank: ACT -> ACT 10 / 9, the board's 82 / 92).
- **The registered rank ok.** `trrd_ok` / `tfaw_ok` are registers; an ACT's
  fire reads them one slot late (ACT -> ACT 3 against t_rrd 2). Carried as the
  model's own view of the last four ACT slots, so the live bank timers are not
  delayed with it.

## 3. The drain close, found by the SKU's own cells

The first pipeline draft requested every ACT after an auto-precharge at its
timer (the measured close-page rule applied to all APs). The SKU's `col_major`
cells fell to -19.9 / -13.8 / -8.4 percent (bl4 / 8 / 16: one drain close per
burst), while every other SKU cell held. The ablation knob `ap_act_la` (arm the
ACT after any AP) put them back to +0.1 / +0.6 / +0.1 -- and broke `close_page`
by +28 percent (the rows 78 -> 100 against the board's 78). One rule cannot
fit both unless it is keyed on what differs: the next head's row against the
closed row. `mc_bank_pick`'s decode has exactly that key (the miss branch
reaches `act_la`; the hit branch is a column blocked by the AP), and
`mc_bank_timers` instantiates `LA_AP = (SCHED_CORE == MC_SCHED_BANK_PICK)`.
With the rule in, both presets hold.

## 4. The ablation (the knob-grid method)

Every term changed in turn on the three presets, 15 board cells each
(`model_ramulator2_ddr2_mc021_ablation_2026-11-17.csv`; the default is the
shipped setting):

| variant | SKU in / 30 (mean abs %) | close_page in / 15 (mean) | bank_interleave in / 12 (mean) |
|---|---|---|---|
| **default** (`admit_lag` 3, `pick_la` 2, `rank_ok_lag` 1) | 30 (0.8) | 14 (5.0) | 1 (14.9) |
| `lag4` (the collapsed model's admission) | 30 (1.2, mixed -8.2) | 14 (4.9) | 2 (12.5) |
| `lag0` / `lag2` | 30 (1.0, mixed +5.1) | 14 (4.7) | 2 (13.3) / 2 (12.1) |
| `la0` (no lookahead, no hint) | 22 (6.6, col_major_bl4 -32.5) | 5 (14.0) | 11 (5.1) |
| `la1` | 22 (5.4) | 3 (16.3) | 4 (12.1) |
| `la3` | 30 (1.4, mixed +9.9) | 10 (8.8) | 7 (11.7) |
| `rankok0` (ACT -> ACT at t_rrd) | 30 (1.0) | 10 (13.5, +60 on interleaved_bl4) | 0 (57.9, +71) |
| `apactla` (RTL question 1: arm the same-row ACT after an AP) | 30 (0.8) | 4 (20.6, rows +28.6) | 1 (14.9) |
| `apstale` (RTL question 2: the closed column's pair masked) | 30 (0.8) | 14 (3.2) | 10 (6.8) |
| `laneoff` | 20 (4.0) | 13 (7.1) | 1 (14.4) |
| `reqfull` | 30 (1.0) | 14 (5.4) | 2 (15.1) |
| `capburst` | 30 (0.8) | 14 (5.2) | 1 (14.9) |

Read as the knob grid taught: `la0` lands `bank_interleave` (11 / 12) and
breaks `close_page` (5 / 15) and the SKU (22 / 30) -- a knob that must flip per
preset is a missing term, not a setting. `apstale` improves two presets and
leaves the SKU alone, but it is the RTL change of question 2, not the RTL
(section 6). `admit_lag` 3 against 4 is the SKU's mixed cell (+1.7 against
-8.2) and the RTL's count with the request register made explicit; the two
presets do not separate them.

## 5. The residual: `bank_interleave` at -15 percent

Eight banks, close page, one column per bank per round: the model's row-hit
cells sit at 197-202 MB/s against the board's 232-238 (4.0 cycles per beat
against the proxy's 3.4). The structure is the RTL's; the difference is where
the stale mask engages, which section 1 showed depends on how many schedulable
entries each bank holds at its fire. In the probe window bank 0's write queue
is empty for a third of the cycles and never above one while the pool stays at
15-16; the model's banks hold one to three (the debug print `depth`), so the
re-picked stale column finds a same-row entry behind it more often and costs
the second slot. Two things feed the RTL's shallower banks: the lane's held
pair (bank 3 in the window) is masked from the main select for the whole
64-cycle window and never served, so its bank accumulates entries at the
others' expense; and a write entry is schedulable only once its data has
landed (the store's `r_wr_fdone`, two cycles after the push in the probe).
The model serves its held pair once a rotation and admits a beat as
schedulable `admit_lag` slots after acceptance. A pool sweep brackets the
effect: pool 8 gives 260, pool 10 215, pool 12 208, pool 16 199-202 -- the
board's 234 is what eight to ten schedulable entries would give. Not tuned: the pool is 16 and the
lane rule is the RTL's; the open question is the exact masking of the held lane
pair (the probe shows it masked in cycles where `w2_any_col_ok` reads 0,
which the rule as read does not explain) and the write fill's reach. Recorded
in MC-021 as the next step.

The other out-of-tolerance cells: `close_page col_major_interleaved_bl16` (board
180 / 240, model 175 / 176: the board's reads run a third faster than its
writes there and the model's do not -- the read path after a read AP, not
measured yet) and `bank_interleave col_major_bl4` (board 195 / 239, model 240 /
195: the same read / write asymmetry, the other way).

## 6. The two RTL questions, priced

- **Arm the same-row ACT after an auto-precharge** (`ap_act_la`): the
  lookahead reaching the AP's tWR-then-tRP for a head that hits the closing
  row. `close_page` single-bank streams +28 percent (the rows 78 -> 100 MB/s,
  the incrementals 83 -> 102 / 93 -> 117), `bank_interleave` 0, the SKU 0. The
  change is in `mc_bank_timer`'s LA_AP reach or the decode's hit branch; it
  pays only where every column closes its row.
- **Skip the closed column's pair in the select** (`ap_stale`): a column that
  auto-precharges marks its pair self-stale as a row command does, so the
  select does not re-pick it in the slot after. `bank_interleave` +20 percent
  (197-202 -> 240-244 on the row-hit cells, into tolerance), `close_page`
  interleaved cells +15 / +12 / +5 (bl4 / 8 / 16), `row_thrash` +10, `random`
  +6, the SKU 0. One AND term on the
  stale mask's D input (`w_stale_if |= cmd_ap`), in the fire cone that MC-011
  kept to D inputs only; whether it fits the 100 MHz cone is the build's to
  say.

Both run `TEST_DUAL` both ways and the formal tasks under
`formal/mc_common/mc_bank_pick` before any board build.

## Method

- The RTL probe is `PERF_PICK_PROBE` + `PERF_PICK_PROBE_FROM=<aclk cycle>` on
  `test_granite_char_perf.py` under `TEST_ADDR_SCHEME=2 TEST_PAGE_POLICY=2`
  (the host's `bank_interleave` pair); the 2026-11-17 run's dump
  (`pick_p9.json`, 64 rows from 60000) carries `r_req`, `r_self_stale`,
  `r_is_col`, `w_sel_src`, `w_pick_pair`, the winner, `w_class_ok` /
  `w_timer_ok` / `w_dmd_fire` / `w_hold_next` / `w_spec_vld`, the hint, the
  lane's `r2_*` / `w2_*`, `bank_act_ready_i`, `bank_row_active_i`, the store's
  `st_wq_cnt0/1` and `wr_head_i[0/1]`. Decode `wr_head_i` as `mc_head_rec_t`
  (bit 44 = vld).
- The model's trace is `GRANITE_SKU_DEBUG=<from_ck>:<to_ck>`: per slot the
  request registers (`*` = masked), the winner and its fate (FIRE / hold /
  wait / stale), the pick and its source (1 hint, 2 CDIR, 3 COL, 4 ROW), the
  lane, the hint, the per-bank queue depths, every admission. Line the two up
  at the same slot of the same cadence; the first slot where the select's
  branch differs names the rule.
- The ablation is `scratchpad/mc021/grid2.py` + `score2.py` (the knob grid's
  driver with a variant dict): 675 cells in 129 s on 40 processes.

## Files

- `projects/components/mem-ctrl-ip/references/ramulator2/overlay/src/ramulator/controller/impl/granite_sku_controller.cpp`
  -- the pipelined controller (knobs `pick_la`, `rank_ok_lag`, `ap_act_la`,
  `ap_stale`; `hop_lag` / `col_row_lag` / `hold_winner` never shipped).
- `bin/char_model.py` -- the knobs on `ModelConfig`, SKU `admit_lag` 3, the
  variants `sku_la0/la1/la3/rankok0/apactla/apstale/lag4`.
- `tests/test_char_model.py` -- the SKU asserts the pipeline's measured values.
- `model_ramulator2_ddr2_granite_sku100{,_bi,_close}_mc021_2026-11-17.csv`,
  `compare_model_sku_vs_board_sku100def_mc021_2026-11-17.md` (45 in / 12 out),
  `model_ramulator2_ddr2_mc021_ablation_2026-11-17.csv`,
  `model_mc021_ablation_2026-11-17.md`.
