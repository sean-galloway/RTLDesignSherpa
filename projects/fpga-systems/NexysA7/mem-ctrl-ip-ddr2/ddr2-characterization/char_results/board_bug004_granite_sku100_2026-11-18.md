# Board: the granite SKU at 100 MHz with the global timers exact (memory-controllers BUG-004), 2026-11-18

Nexys A7-100T (JTAG serial 210292BFA3EE), `GRANITE_SYS_100=1 make bitstream` on the
BUG-004 RTL (`fpga/bitstream/ddr2_char_granite_sku100_bug004_2026-11-18.bit`,
WNS +0.029 ns under the 0.2 ns clock-uncertainty budget, 0 failing endpoints,
37,297 LUT / 32,918 FF; the 11-16 SKU build was 37,357 / 32,918 at +0.012).
Host defaults (lane on, pool 16, JEDEC counts from `ddr2_timings_mc_cycles` at
100 MHz: tRRD 2, tFAW 5, tCCD 1, tWTR 4, tRTW 21 with `rtw_guard` 7).

Smoke: init PASS (324 s), write_read PASS, memtest PASS 32 / 32 chunks over 128 MB.
`--profile every --txn-scale 4000`: 72 runs (68 distinct config x scenario cells), **0 mismatched beats**, every
cell ok.

## What the fix did on the board

The same 68 cells against the 2026-11-16 SKU set (the last board run before the
fix; same bitstream family, same host). Write / read MB/s at 100 MHz.

| preset | scenario | 11-16 wr / rd | BUG-004 wr / rd | delta |
|---|---|---|---|---|
| defaults | incremental_bl4 | 775 / 776 | 775 / 776 | +0.0 / +0.0 % |
| defaults | incremental_bl8 | 775 / 776 | 775 / 776 | -0.0 / -0.0 % |
| defaults | incremental_bl16 | 775 / 776 | 775 / 776 | +0.0 / +0.0 % |
| defaults | row_major_bl4 | 775 / 778 | 775 / 778 | -0.0 / +0.0 % |
| defaults | row_major_bl8 | 775 / 778 | 775 / 778 | +0.0 / +0.0 % |
| defaults | row_major_bl16 | 775 / 778 | 775 / 778 | +0.0 / -0.0 % |
| defaults | col_major_bl4 | 283 / 389 | 283 / 389 | -0.0 / +0.0 % |
| defaults | col_major_bl8 | 416 / 520 | 416 / 520 | +0.0 / +0.0 % |
| defaults | col_major_bl16 | 541 / 623 | 541 / 623 | +0.0 / +0.0 % |
| defaults | col_major_interleaved_bl4 | 765 / 763 | 765 / 762 | +0.0 / -0.2 % |
| defaults | col_major_interleaved_bl8 | 768 / 768 | 768 / 767 | -0.0 / -0.1 % |
| defaults | col_major_interleaved_bl16 | 772 / 770 | 772 / 770 | +0.0 / +0.0 % |
| defaults | col_major_bl8_multiid | 416 / 520 | 416 / 520 | +0.0 / +0.0 % |
| defaults | col_major_bl8_gap | 376 / 400 | 376 / 400 | +0.0 / +0.0 % |
| defaults | incremental_bl8_multiid | 775 / 776 | 775 / 776 | +0.0 / +0.0 % |
| defaults | row_major_bl8_multiid | 775 / 778 | 775 / 778 | +0.0 / +0.0 % |
| defaults | col_major_interleaved_bl8_multiid | 768 / 768 | 768 / 767 | +0.0 / -0.1 % |
| open_page | incremental_bl4 | 775 / 778 | 775 / 778 | -0.0 / +0.0 % |
| open_page | incremental_bl8 | 775 / 778 | 775 / 778 | -0.0 / +0.0 % |
| open_page | incremental_bl16 | 775 / 778 | 775 / 778 | +0.0 / +0.0 % |
| open_page | row_major_bl4 | 775 / 778 | 775 / 778 | +0.0 / +0.0 % |
| open_page | row_major_bl8 | 775 / 778 | 775 / 778 | -0.0 / +0.0 % |
| open_page | row_major_bl16 | 775 / 778 | 775 / 778 | -0.0 / +0.0 % |
| open_page | col_major_bl4 | 283 / 389 | 283 / 389 | +0.0 / +0.0 % |
| open_page | col_major_bl8 | 416 / 520 | 416 / 520 | +0.0 / +0.0 % |
| open_page | col_major_bl16 | 541 / 623 | 541 / 623 | -0.0 / +0.0 % |
| open_page | col_major_interleaved_bl4 | 768 / 768 | 767 / 767 | -0.2 / -0.1 % |
| open_page | col_major_interleaved_bl8 | 770 / 770 | 770 / 770 | -0.0 / +0.0 % |
| open_page | col_major_interleaved_bl16 | 772 / 774 | 772 / 774 | +0.0 / +0.0 % |
| open_page | col_major_bl8_multiid | 416 / 520 | 416 / 520 | +0.0 / +0.0 % |
| open_page | col_major_bl8_gap | 376 / 400 | 376 / 400 | +0.0 / +0.0 % |
| open_page | incremental_bl8_multiid | 775 / 778 | 775 / 778 | -0.0 / +0.0 % |
| open_page | row_major_bl8_multiid | 775 / 778 | 775 / 778 | +0.0 / +0.0 % |
| open_page | col_major_interleaved_bl8_multiid | 770 / 770 | 770 / 770 | -0.0 / +0.0 % |
| close_page | incremental_bl4 | 82 / 92 | 82 / 92 | +0.2 / -0.0 % |
| close_page | incremental_bl8 | 82 / 92 | 82 / 92 | +0.2 / -0.0 % |
| close_page | incremental_bl16 | 82 / 92 | 82 / 92 | +0.1 / -0.0 % |
| close_page | row_major_bl4 | 78 / 87 | 78 / 87 | +0.0 / +0.0 % |
| close_page | row_major_bl8 | 78 / 87 | 78 / 87 | +0.0 / +0.0 % |
| close_page | row_major_bl16 | 78 / 87 | 78 / 87 | +0.0 / +0.0 % |
| close_page | col_major_bl4 | 82 / 92 | 82 / 92 | +0.0 / +0.0 % |
| close_page | col_major_bl8 | 80 / 90 | 80 / 90 | +0.0 / +0.0 % |
| close_page | col_major_bl16 | 79 / 88 | 79 / 88 | +0.0 / +0.0 % |
| close_page | col_major_interleaved_bl4 | 235 / 232 | 379 / 387 | +61.2 / +67.0 % |
| close_page | col_major_interleaved_bl8 | 213 / 219 | 251 / 328 | +17.7 / +50.0 % |
| close_page | col_major_interleaved_bl16 | 180 / 240 | 171 / 240 | -5.0 / +0.0 % |
| close_page | col_major_bl8_multiid | 80 / 90 | 80 / 90 | +0.0 / +0.0 % |
| close_page | col_major_bl8_gap | 80 / 90 | 80 / 90 | +0.0 / +0.0 % |
| close_page | incremental_bl8_multiid | 82 / 92 | 82 / 92 | +0.2 / -0.0 % |
| close_page | row_major_bl8_multiid | 78 / 87 | 78 / 87 | +0.0 / +0.0 % |
| close_page | col_major_interleaved_bl8_multiid | 213 / 221 | 251 / 328 | +17.7 / +48.1 % |
| bank_interleave | incremental_bl4 | 238 / 233 | 387 / 387 | +62.6 / +65.9 % |
| bank_interleave | incremental_bl8 | 234 / 233 | 387 / 386 | +65.7 / +66.1 % |
| bank_interleave | incremental_bl16 | 238 / 233 | 387 / 386 | +62.7 / +65.5 % |
| bank_interleave | row_major_bl4 | 238 / 233 | 387 / 387 | +62.7 / +66.3 % |
| bank_interleave | row_major_bl8 | 238 / 232 | 387 / 387 | +62.7 / +66.8 % |
| bank_interleave | row_major_bl16 | 238 / 232 | 387 / 387 | +62.7 / +66.8 % |
| bank_interleave | col_major_bl4 | 195 / 239 | 258 / 351 | +32.6 / +46.6 % |
| bank_interleave | col_major_bl8 | 237 / 235 | 387 / 387 | +63.3 / +64.4 % |
| bank_interleave | col_major_bl16 | 238 / 234 | 387 / 387 | +62.7 / +65.5 % |
| bank_interleave | col_major_interleaved_bl4 | 195 / 222 | 242 / 254 | +24.2 / +14.3 % |
| bank_interleave | col_major_interleaved_bl8 | 238 / 234 | 387 / 387 | +62.7 / +65.5 % |
| bank_interleave | col_major_interleaved_bl16 | 238 / 235 | 387 / 387 | +62.6 / +65.0 % |
| bank_interleave | col_major_bl8_multiid | 234 / 236 | 387 / 387 | +65.8 / +64.4 % |
| bank_interleave | col_major_bl8_gap | 238 / 240 | 376 / 387 | +58.1 / +61.3 % |
| bank_interleave | incremental_bl8_multiid | 238 / 233 | 387 / 387 | +62.6 / +66.2 % |
| bank_interleave | row_major_bl8_multiid | 234 / 232 | 387 / 387 | +65.8 / +66.8 % |
| bank_interleave | col_major_interleaved_bl8_multiid | 238 / 234 | 387 / 387 | +62.6 / +65.6 % |

Three things to read off it:

- **Every ACT-bound close-page cell moved to the two-cycle floor.** bank_interleave
  row-hit cells 238 -> 387 (+63 .. +67 percent), close_page col_major_interleaved_bl4
  235 / 232 -> 379 / 387. 387 MB/s is 8 bytes per 2.07 MC cycles: one ACT every
  two cycles with the row lane riding beside the previous column (the proxy
  trace: ACT gap 2, lane fires on two thirds of the ACTs). The model said 388
  before the RTL was touched; the proxy did 387; the board does 387.
- **Nothing else moved.** The SKU's 34 open-page cells and the 9 single-bank
  close_page cells are within 0.2 percent of 11-16: tRRD never binds on an
  open row or on one bank, and tCCD / tWTR / tRTW losing their extra cycle is
  invisible at these turn lengths (tRTW's enforced spacing was kept at 21).
- **The remaining low cells are read / write asymmetries, not the ACT rate:**
  bank_interleave col_major_bl4 258 / 351 and col_major_interleaved_bl4 242 / 254,
  close_page col_major_interleaved_bl8 251 / 328 and bl16 171 / 240. These are
  the cells MC-021 step 1 already named as unmeasured (the read path after a
  read AP); they are the model's residual now.

## The model against this set

`compare_model_sku_vs_board_sku100bug004_2026-11-18.md`: the SKU model with its
fixed default (`rank_ok_lag 0`) beside these cells, **45 in / 3 out** of 48
(the 11-17 compare was 45 / 12, with all 12 bank_interleave cells out at -13 ..
-17 percent). bank_interleave row-hit cells +0.3 .. +0.5 percent. Out:
bank_interleave col_major_bl4 (+29 / -5: the board's write side is 258 against
the model's symmetric 333), col_major_bl8 (-14), col_major_interleaved_bl16
(-10). The `windows` profile (mixed, row_thrash, random) is in the final-RTL section
below.

## Record

- 07:03 `GRANITE_SYS_100=1 make bitstream` (first BUG-004 RTL) -> 07:19, met.
- 07:21 program, 07:21-07:27 smoke ALL PASS, 07:27-07:35 `--profile every`.
- The obs_* debug-flag alignment (the formal's Family 2) landed in the RTL after
  this build; it changes only the STALL_* attribution flags. The final RTL is
  rebuilt and re-run below.

## The final RTL: `ddr2_char_granite_sku100_bug004b_2026-11-18.bit`

`GRANITE_SYS_100=1 make bitstream` on the committed RTL (obs_* flags included):
WNS +0.029, 0 failing, 37,297 LUT / 32,918 FF -- the same numbers. Programmed
07:46 (a first program at 07:43 left the Nexys UART re-enumerated, ttyUSB2 ->
ttyUSB1, and the harness got no reply from the port until the board was
programmed again; nothing to do with the design). Smoke ALL PASS (memtest 32 /
32). `--profile every`: 68 cells, 0 mismatched, every cell within 0.4 percent
of the first BUG-004 run (`char_granite_sku100bug004b_every_2026-11-18.csv`).
`--profile windows` (`char_granite_sku100bug004b_windows_2026-11-18.csv`),
9 cells, 0 mismatched, against 11-16:

| preset | scenario | 11-16 wr / rd | BUG-004 wr / rd | delta |
|---|---|---|---|---|
| defaults | mixed_bl8 | 272 / 272 (union 543) | 269 / 269 (union 537) | -1.1 % |
| defaults | row_thrash_bl8 | 770 / 770 | 768 / 766 | -0.3 / -0.5 % |
| defaults | random_bl8 | 718 / 740 | 719 / 739 | +0.1 / -0.1 % |
| open_page | mixed_bl8 | 272 / 272 (union 545) | 272 / 273 | 0 |
| open_page | row_thrash_bl8 | 770 / 770 | 770 / 770 | 0 |
| open_page | random_bl8 | 726 / 746 | 726 / 745 | 0 |
| close_page | mixed_bl8 | 73 / 152 (union 145) | **56 / 56 (union 111)** | **-23 % (union)** |
| close_page | row_thrash_bl8 | 208 / 197 | **246 / 251** | +18 / +28 % |
| close_page | random_bl8 | 188 / 207 | **204 / 234** | +8 / +13 % |

close_page row_thrash and random gain what their ACT rate allows. close_page
mixed_bl8 LOSES: the 11-16 shape was writes 73 / reads 152 (reads favoured),
the fixed shape is 56 / 56. The model predicted exactly this cell (54 / 54,
union 107) before the board ran, so the mechanism is in the model: four writers
and four readers on the same banks eight rows apart under close page, and with
the row lane now able to fire the waiting direction's ACT rides beside the
holder's column and the two directions precharge each other's rows (the
ISSUE-004 shape, which open page escapes because its turns are 255 columns).
It is one corner cell at a seventh of the SKU's mixed figure either way; it is
recorded in MC-021 as the next thing to measure, not papered over here.

The model against the complete final set (every + windows):
`compare_model_sku_vs_board_sku100bug004b_2026-11-18.md`, **53 in / 4 out** of
57 (11-17: 45 / 12). Out: bank_interleave col_major_bl4 (+29 / -5),
col_major_bl8 (-14), col_major_interleaved_bl4 (+2 / +10), col_major_interleaved_bl16
(-10) -- the read / write asymmetric col_major cells. close_page mixed is IN at
-3.9 percent.
