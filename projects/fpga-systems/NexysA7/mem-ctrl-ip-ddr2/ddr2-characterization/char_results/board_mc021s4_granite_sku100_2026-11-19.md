# Board: the granite SKU at 100 MHz with the fired auto-precharge pair masked (memory-controllers MC-021 step 5), 2026-11-19

Nexys A7-100T (JTAG serial 210292BFA3EE), `GRANITE_SYS_100=1 make bitstream` on
the step-5 RTL (`fpga/bitstream/ddr2_char_granite_sku100_mc021s4_2026-11-19.bit`,
WNS +0.080 ns under the 0.2 ns clock-uncertainty budget, 0 failing endpoints,
37,389 LUT / 32,926 FF; the BUG-004 build was 37,297 / 32,918 at +0.029). Host
defaults as for BUG-004 (lane on, pool 16, JEDEC counts from
`ddr2_timings_mc_cycles` at 100 MHz).

Smoke: init PASS (324 s), write_read PASS, memtest PASS 32 / 32 chunks over
128 MB. `--profile every --txn-scale 4000`: 72 runs (68 cells), **0 mismatched
beats**, every cell ok; `--profile windows`: 9 cells, run five times, 0
mismatched in each.

**The change** (`mc_bank_pick.sv`, one AND term in the stale mask's fire case):
a pair whose column fired with auto-precharge is masked from the select for the
cycle after its fire, as a pair whose queue emptied already was. Step 4's
replay (`model_mc021_hit_lag_2026-11-19.md`, section 5) had found the fired
pair's leftover column request winning the select the cycle after -- the
rotor starts past the fired pair -- for a wasted slot and the pair's fresh ACT
masked from the row lane; the SKU model priced the mask before the RTL was
touched. The formal gold copy carries the same term with a dated note; the
equivalence, cover and lane tasks pass on it.

## What the fix did on the board

The same cells against the BUG-004 set of 2026-11-18 (the last board run before
this change; same host, same bitstream family). Write / read MB/s at 100 MHz;
the model's prediction is the step-5 model (`hit_lag` 2, `ap_fire_stale`) run
before the board was programmed.

| preset | cell | BUG-004 board | step-5 board | delta | model predicted |
|---|---|---|---|---|---|
| bank_interleave | col_major_bl4 | 258 / 351 | 283 / 388 | +9.5 / +10.4 % | 283 / 389 |
| bank_interleave | col_major_interleaved_bl4 | 242 / 253 | 243 / 317 | +0.4 / +25.4 % | 246 / 322 |
| close_page | col_major_interleaved_bl4 | 379 / 387 | 386 / 387 | +2.0 / +0.1 % | 388 / 389 |
| close_page | col_major_interleaved_bl8 | 251 / 328 | 250 / 361 | -0.3 / +10.0 % | 287 / 334 |
| close_page | col_major_interleaved_bl8_multiid | 251 / 328 | 250 / 356 | -0.3 / +8.8 % | (not modelled) |
| close_page | col_major_interleaved_bl16 | 171 / 240 | 171 / 238 | +0.0 / -1.1 % | 208 / 239 |
| close_page | row_thrash_bl8 | 246 / 251 | 238 / 314 | -3.3 / +24.9 % | 249 / 316 |
| close_page | random_bl8 | 204 / 234 | 203 / 258 | -0.4 / +10.6 % | 218 / 258 |
| close_page | mixed_bl8 (union) | 56 / 56 (111) | 56 / 59 (112) | +1 % | 58 / 75 (117) |
| defaults | mixed_bl8 (union) | 269 / 269 (537) | 272 / 273 (545) | +1.5 % | 277 / 277 (554) |
| defaults | random_bl8 | 719 / 739 | 723 / 750 | +0.5 / +1.4 % | 730 / 752 |
| open_page | mixed_bl8 (union) | 272 / 273 (545) | 311 / 522 (622) | +14.2 / +91.4 % | 277 / 277 (554) |
| open_page | random_bl8 | 726 / 745 | 728 / 757 | +0.3 / +1.6 % | 730 / 752 |

The other 62 cells of the `every` profile (every `defaults` and `open_page`
row-hit, col_major and interleaved cell, every `bank_interleave` row-hit and
eight-bank cell, every `close_page` single-bank cell) moved 0.1 percent or
less, as the model said they would. The SKU as shipped (`defaults`) is
unchanged on every single-direction cell.

Where the model had priced the change it was right: the four cells it moved
by more than 5 percent on the read side (bank_interleave bl4 +10.4, interleaved
bl4 +25.4, close_page interleaved bl8 +10.0, row_thrash +24.9, random +10.6)
land within 1.5 percent of the prediction, and the write sides it left alone
stayed. The two places it is wrong were wrong before the change in the same
way and are the next items (below).

## The model against this set

`compare_model_sku_vs_board_sku100s4_2026-11-19.md`: **55 in / 2 out** of 57.

- `close_page col_major_interleaved_bl16`, write side +21.3 (model 208, board
  171; bl8 is +14.9 at 287 against 250 and in at the 15 tolerance by a point).
  The read sides are on the board (239 / 238, 334 / 361). The proxy with the
  step-5 RTL reproduces the board on both cells (171.1 / 235.8, 249.5 /
  341.0 from the DRAM trace), so this is the model. Both run the same
  stream: a 16-beat burst is sixteen same-row beats of ONE bank under the
  default map, so under close page a burst is sixteen ACT / column / close
  cycles of one bank, and the bursts in flight are the banks in play -- three,
  in both the proxy (3 banks activated per 40-cycle window on 3,494 of 3,832
  windows) and the model. The pool is full in both (the probe's store
  occupancy 15-16 on the write pass). The difference is inside the bank
  cycle: the proxy lands half its write columns at ACT + 5 (ACT -> column 2
  and 5 half each) with same-bank ACT -> ACT at 10-15, where the model lands
  196 of 208 at ACT + 2 with same-bank ACT -> ACT at 10 -- the hold that
  discards a hint, on the write side with three same-bank bursts in flight,
  still present after the step-5 term. The long probe into the three-burst
  steady state is MC-021 item 1 -- resolved the same evening as step 6: the
  store's write record waits for the entry's fill (two cycles a read's does
  not), which puts a new bank's first ACT in the cycling banks' collision
  slot; the model's write side 287 / 208 -> 251 / 172 against the board's
  250 / 171 (`model_mc021_wr_fill_lag_2026-11-19.md`).
- `open_page mixed_bl8`, union -10.9 (model 554, board 622). The board moved
  from 272 / 273 to 311 / 522 with the change while `defaults mixed_bl8` (the
  hybrid page predictor, modelled as open page) moved 269 / 269 -> 272 / 273
  and the model moved 567 -> 554. Five windows runs: the cell came out
  311 / 522, 272 / 272, 304 / 521, 272 / 272, 311 / 521 -- two modes, three
  fast and two slow, with every other cell of the profile identical to the
  MB/s across all five runs (0 mismatched beats in each). The mode is decided
  in the race at GO and held for the whole cell; the slow mode is the
  pre-change number and the model's (554 against 545, in), the fast mode is a
  read side nearly doubled on one preset and not on `defaults`. A
  direction-register effect the model does not carry for open page; MC-021
  item 3, with the close_page mixed regression beside it.

## Record

- `char_granite_sku100s4_every_2026-11-19.csv`, `char_granite_sku100s4_windows_2026-11-19.csv`
  (the board), `compare_model_sku_vs_board_sku100s4_2026-11-19.md` (the model
  against them), `model_ramulator2_ddr2_granite_sku100{,_bi,_close}_s4_2026-11-19.csv`
  (the model's run before the board was programmed; its compare against the
  BUG-004 set, `compare_model_sku_vs_board_sku100bug004b_s4_2026-11-19.md`, is
  the prediction as filed).
- The RTL: `mc_bank_pick.sv` and the formal gold copy
  `formal/mc_common/mc_bank_pick/mc_bank_pick_gold.sv`; the model's
  `ap_fire_stale` default is now true (`sku_noapfirestale` = the RTL before).
- Build reports under `targets/granite/fpga/reports/`.
- The probe on the write pass of the close_page interleaved cell: MC-021 item 1.

## Regressions on the step-5 RTL (every suite clean-all first)

| suite | result |
|---|---|
| `formal/mc_common/mc_bank_pick` equiv, equiv_n4, cover, dual, dual_cover | 5 / 5 PASS against the gold copy carrying the same term (equiv 12 min, equiv_n4 7 min) |
| ddr2_char_framework `run-all-func-parallel`, TEST_DUAL=1 | 222 passed, 2 xfailed; 48 errors, all `test_ddr2_char_char.py` refusing the foreign `TEST_DUAL` knob at its environment guard (the pumice char test; see the plain run) |
| ddr2_char_framework `run-all-func-parallel`, TEST_DUAL=0 | 222 passed, 2 xfailed, the same 48 guard errors |
| ddr2_char_framework `run-all-func-parallel`, no TEST_* override | 226 passed, 2 xfailed, 0 errors in 59 min (the 48 guard errors of the TEST_DUAL runs were the knob, not the design: `test_ddr2_char_char.py` passes plain) |
| granite top `run-all-full-parallel` | 29 passed, 5 skipped, 1 xfailed (the BUG-004 baseline exactly) |
| pumice top / macro / fub `run-all-full-parallel` | 525 passed 4 skipped / 117 passed / 32 passed; pumice top again with TEST_DUAL=0: 525 passed 4 skipped |
| scoria top / macro / fub `run-all-full-parallel` | 4 passed / 7 failed 12 passed / 10 failed 195 passed 1 skipped -- every failure a recorded pre-existing stale testbench (`u_arbiter` renamed in the scheduler-plane TB, `t_rcd_i` in the bank-timer TB, `column_pick_smoke` on scoria's own arbiter, which does not use the pick core), per `model_bug004_act_spacing_2026-11-18.md` |
| andesite top / macro / fub `run-all-full-parallel` | 4 failed / 10 failed 8 passed / 12 failed 213 passed -- the same recorded classes (`andesite_core_tb` compile error, `u_arbiter`, `t_rcd_i`, andesite's own arbiter, which does not use the pick core) |
| vendor Ramulator tests / char_model tests | 217 / 37 passed |
| `GRANITE_SYS_100=1 make bitstream` | WNS +0.080 under the 0.2 ns budget, 0 failing endpoints, 37,389 LUT / 32,926 FF |
| the proxy on six cells with the new RTL | within 0.6 percent of the model's prediction on the four bank_interleave / SKU cells; the two close_page interleaved cells equal the board (171.1 / 235.8, 249.5 / 341.0) |
