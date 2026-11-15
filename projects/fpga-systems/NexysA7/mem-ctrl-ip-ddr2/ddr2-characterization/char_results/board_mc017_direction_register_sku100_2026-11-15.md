# The direction-register fix on the Nexys A7 at 100 MHz (memory-controllers MC-017 board half, 2026-11-15)

The sim half (`sim_mc017_direction_register_2026-11-15.md`) found that on
granite's `mixed` window every cap flip handed the register to the waiting
direction for five cycles and no columns, fixed it with four register-only
terms in `mc_bank_pick`, and measured the fair window at 272 / 273 MB/s
(lane on) and 264 / 265 (lane off) with the worst read wait 520 cycles where
it was 52 000. This is the board: the sys100 SKU built with the row lane
(MC-014) and `GRANITE_NUM_ENTRIES=16` (MC-015's recommended point), timing
under the 0.2 ns clock-uncertainty budget (MC-011), smokes, then the char
`windows` suite with the lane on and off and `every` with the lane on,
against the 2026-11-13 cells of the same build without the fix.

## Timing and area

| build | pool | lane | LUT | FF | WNS (ns, under the 0.2 ns budget) | failing endpoints | worst path |
|---|---|---|---|---|---|---|---|
| MC-015 (2026-11-13) | 16 | built | 37 258 | 32 922 | +0.034 | 0 | main pick `r_req` -> `r_win_cls` |
| this build | 16 | built | 37 357 | 32 918 | **+0.012** | **0** | main pick `r_is_col` -> `r_win_cls` (+0.012), lane pick `r_is_col` -> `r2_pair` (+0.019) |

+99 LUT for the four terms (the hint's direction gate, the drain flip's
hold and row-request terms, the lane's per-direction column-pending split);
the worst path is still the pick core's select cone into the winner class,
now with the lane's pick second. Closed, at the thin end of the placement
spread the budget exists for (MC-011: +0.034 and +0.059 on the two builds
before it). Reports `targets/granite/fpga/reports_sys100_mc017_n16_2026-11-15`;
bitstream `fpga/bitstream/ddr2_char_granite_sku100_n16_mc017_2026-11-15.bit`
(untracked).

## Smoke

`init write_read memtest`, lane off and lane on: ALL PASS (init 324 s,
memtest 15 s, as every build since 2026-11-12).

## `windows`, lane on (pool 16; wr / rd MB/s, union = both directions over the longer window)

| scenario | preset | 2026-11-13 (no fix) | with the fix |
|---|---|---|---|
| mixed_bl8 | defaults | 318 / 649 (union 635) | **272 / 272 (543)** |
| mixed_bl8 | open_page | 473 / 286 (union 571) | **272 / 272 (545)** |
| mixed_bl8 | close_page | 69 / 115 (139) | 72 / 152 (145) |
| random_bl8 | defaults / open_page | 718 / 740, 726 / 746 | 718 / 740, 726 / 746 |
| row_thrash_bl8 | defaults / open_page | 770 / 770 | 770 / 770 |
| random_bl8, row_thrash_bl8 | close_page | 188 / 207, 213 / 197 | 188 / 207, 208 / 197 |

The sim said 272 / 273 and 272 / 272; the board says 272 / 272 on both
presets. The bimodal pair (which direction held the first batch decided
which cell was 649 and which 286-318) is gone: the two presets now give the
same cell to the MB/s, and the two directions the same number. The union
is 14 percent under the `defaults` sequential shape and 5 percent under the
`open_page` one -- the fairness price the sim half priced on this synthetic
window (the old register ran the writes alone and then the reads alone;
here every turn pays the turnaround and the writers' per-burst row switch).
`random` and `row_thrash` are identical to the MB/s: the register never
flips on a single-direction window.

## `windows`, lane off (pool 16 with the fix, against the pool-8 lane-off cells of 2026-11-12: the shipped SKU's shape)

| scenario | preset | pool 8, no fix (2026-11-12) | pool 16 with the fix |
|---|---|---|---|
| mixed_bl8 | defaults | 260 / 319 (union 520) | **262 / 262 (524)** |
| mixed_bl8 | open_page | 262 / 330 (union 525) | **279 / 279 (557)** |
| mixed_bl8 | close_page | 48 / 48 (96) | 62 / 113 (124) |
| random_bl8 | defaults / open_page | 628 / 658, 635 / 661 | 651 / 653, 655 / 655 |
| row_thrash_bl8 | defaults / open_page | 684 / 688, 688 / 688 | 680 / 680, 683 / 684 |

With the lane off the union holds or gains (+1 / +6 percent on `mixed`) and
the cells are symmetric; `random` gains 3 percent (the deeper pool, MC-015)
and `row_thrash` gives back 0.6 percent (the pool's known column-stream
cost, MC-015's lane-off control). The 2026-11-12 column is pool 8, so this
is not a one-variable comparison; the sim half's lane-off cell at pool 8
(264 / 265, union 528 against 524) is.

## `every`, lane on (73 cells against 2026-11-13, pool 16 lane on)

61 of 68 shared cells within 2 MB/s, every `defaults` and `open_page` cell
among them (`col_major_interleaved` 768-772 / 768-774, `row_major` 775 /
778, `incremental` 775 / 776-778, `col_major` 283-541 / 389-623 unchanged).
The seven that moved are all in the `bank_interleave` and `close_page`
presets, by 4-12 MB/s either way and one up by 27 (`bank_interleave
col_major_interleaved_bl4` reads 195 -> 222); those presets alternate the
register on single-id streams and are the irrelevant presets they were.
0 mismatched beats and `ok` on every cell of all three runs.

## What this means for the SKU

The fix removes a 520 us read starvation on any window with both directions
live and makes the two directions share the bus; on this synthetic `mixed`
window that costs 5-14 percent of the aggregate with the lane on and gains
1-6 percent with it off. Nothing single-direction moves. The RTL change
ships in the common pick core (pumice shares it; its suites pass). Whether
the sys100 SKU takes the lane and the 16-entry pool together (MC-015's
recommendation) is still the owner's decision; this build is that point
with the fix, closed at +0.012 ns.

## Recipe

    cd projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/targets/granite
    GRANITE_SYS_100=1 GRANITE_DUAL_ISSUE=1 GRANITE_NUM_ENTRIES=16 make bitstream
    make program BITSTREAM=fpga/bitstream/ddr2_char_granite_sku100_n16_mc017_2026-11-15.bit
    make run SEQUENCES="init write_read memtest" RUN_ARGS="--controller granite"                       # smoke, lane off
    TEST_DUAL_ISSUE=1 make run SEQUENCES="init write_read memtest" RUN_ARGS="--controller granite"     # smoke, lane on
    TEST_DUAL_ISSUE=1 make run SEQUENCES="init char" RUN_ARGS="--controller granite --profile windows --txn-scale 4000 --char-csv <char_results>/char_granite_sku100n16fix_windows_2026-11-15.csv"
    make run SEQUENCES="init char" RUN_ARGS="--controller granite --profile windows --txn-scale 4000 --char-csv <char_results>/char_granite_sku100n16fixoff_windows_2026-11-15.csv"
    TEST_DUAL_ISSUE=1 make run SEQUENCES="init char" RUN_ARGS="--controller granite --profile every   --txn-scale 4000 --char-csv <char_results>/char_granite_sku100n16fix_every_2026-11-15.csv"

CSV tags: `sku100n16fix` (lane on) and `sku100n16fixoff` (lane off).
