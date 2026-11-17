# The granite FPGA SKU moves to the measured point: row lane built, 16-entry pool (2026-11-16)

Owner, 2026-11-16, closing the decision MC-015 and MC-017 left open: "The
FPGA SKU is the configuration." The granite defaults became the design point
the board had measured on 2026-11-15 -- the pick core's row lane built
(MC-014), the store pool at 16 entries per direction (MC-015), the MC-017
direction register. Until today that point existed only as a knob build
(`GRANITE_DUAL_ISSUE=1 GRANITE_NUM_ENTRIES=16` in the environment); this
write-up is the proof that the no-knob build is the same machine.

## What moved

| where | was | now |
|---|---|---|
| `granite_pkg.sv` `GRANITE_SEAM_N` (the pool; `granite_core` / `granite_top_geared` `NUM_ENTRIES` default) | 8 | 16 |
| `granite_core` / `granite_top_geared` `DUAL_ISSUE` default | 0 | 1 |
| `granite_char_harness` / `granite_char_macro` / `granite_char_uart_tb_top` `NUM_ENTRIES`, `DUAL_ISSUE` | 8, 0 | 16, 1 |
| board knob `GRANITE_DUAL_ISSUE` (create_project.tcl, granite_char_top) | `=1` builds the lane | carries a value; unset = built, `=0` builds it out for a control |
| sim proxy `TEST_DUAL` / `TEST_NUM_ENTRIES` defaults (sim_build tags) | 0 / 8 (`_dual`, `_n<N>`) | 1 / 16 (`_laneoff`, `_n<N>` when not 16) |
| host runtime lane enable (`pumice_char.py` `ControllerConfig.lane_on`) | `TEST_DUAL_ISSUE=1` only | the controller's SKU: granite on, pumice off; `TEST_DUAL_ISSUE` wins, `=0` writes the enable off |

The runtime enable stays with the host rather than the RDL reset: the lane
needs `SCHED_POLICY.dual_issue` and `DFI_PHASE.row_phase` set together and the
host derives its tRTP / tRCD margins from `row_phase`, so the host owns the
pair the way it already owns every timing CSR. Pumice's lane default is
untouched (pumice TASK-047's open decision).

## Timing and area, no knobs

| build | LUT | FF | WNS (ns, under the 0.2 ns budget) | failing endpoints | the knob build it reproduces |
|---|---|---|---|---|---|
| `GRANITE_SYS_100=1 make bitstream` | 37 357 | 32 918 | **+0.012** | 0 | MC-017 2026-11-15: 37 357 / +0.012 / 0 -- identical |
| `make bitstream` (sys75, the 75 MHz profile) | 37 012 | 32 919 | **+0.967** | 0 | first build of this point at 75 MHz |

Reports: `targets/granite/fpga/reports_sys100_sku_2026-11-16`,
`reports_sys75_sku_2026-11-16`; bitstreams
`fpga/bitstream/ddr2_char_granite_sku100_2026-11-16.bit`,
`ddr2_char_granite_sku75_2026-11-16.bit` (untracked).

## Board, sys100, host defaults (no TEST_* in the environment)

Smoke `init write_read memtest`: ALL PASS with the host defaults (lane on)
and with `TEST_DUAL_ISSUE=0` (lane off); init 324 s, memtest 15 s, as on
every build since 2026-11-09.

`windows` (four threads) against the MC-017 knob build's lane-on cells of
2026-11-15: every cell identical to the MB/s (`mixed_bl8` 272 / 272 on
`defaults` and `open_page`, `row_thrash_bl8` 770 / 770, `random_bl8` 718 /
740 and 726 / 746), worst delta 0.3 percent on a `close_page` cell, 0
mismatched beats. The `mixed` cell alone proves the lane is on by default:
lane off this window reads 264 / 265.

`every` (73 cells) against the same control: 61 of 69 shared cells within 1
percent, every `defaults` and `open_page` cell among them
(`col_major_interleaved` 768-772 / 768-774, `row_major` 775 / 778,
`incremental` 775 / 776-778, `col_major` 283-541 / 389-623). The eight that
moved are all in the `bank_interleave` and `close_page` presets, by 4-12
MB/s either way and one up by 44 (`bank_interleave col_major_bl4` reads 195
-> 239); the same two presets moved by the same amounts between the 11-13
and 11-15 runs of the same netlist (MC-017's write-up), so this is their
run-to-run band, not the build. 0 mismatched beats and `ok` on every cell.

What the `bank_interleave` history does say, for the record: with the lane
on that preset sits at 234-246 / 233-250 where the lane-off builds give 258 /
258 on every `col_major`, `incremental` and `row_major` cell (2026-11-12 and
11-13 controls), and `col_major_bl4` writes at 195. A 5-9 percent lane cost
on a preset that alternates the direction register on single-id streams; it
was there at pool 8 (`sku100dual5`, 221-246) and is not new today. Recorded,
not acted on: the preset is one of the two "irrelevant" ones, and a lane-off
build is one knob away (`GRANITE_DUAL_ISSUE=0`) if a workload ever looks like
it.

## Sim, defaults

granite top FUNC 25 passed / 5 skipped / 1 xfailed; char framework FUNC 226
passed / 2 xfailed (the proxy now builds the lane and the 16-entry pool by
default; its perf dumps record `dual_issue: 1`); pumice fub 32, macro 78, top
220 / 4 skipped, phy 32 / 4 (unchanged by this, run in the same sweep as
BUG-003). Formal: no common-ip RTL changed.

## Recipe

    cd projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/targets/granite
    GRANITE_SYS_100=1 make bitstream                      # the SKU at 100 MHz: lane built, pool 16, nothing else set
    make bitstream                                        # the SKU at 75 MHz
    GRANITE_SYS_100=1 GRANITE_DUAL_ISSUE=0 make bitstream # the lane-off control
    make program BITSTREAM=fpga/bitstream/ddr2_char_granite_sku100_2026-11-16.bit
    make run SEQUENCES="init write_read memtest" RUN_ARGS="--controller granite"            # host defaults: lane on
    TEST_DUAL_ISSUE=0 make run SEQUENCES="init write_read memtest" RUN_ARGS="--controller granite"
    make run SEQUENCES="init char" RUN_ARGS="--controller granite --profile windows --txn-scale 4000 --char-csv <char_results>/char_granite_sku100def_windows_2026-11-16.csv"
    make run SEQUENCES="init char" RUN_ARGS="--controller granite --profile every   --txn-scale 4000 --char-csv <char_results>/char_granite_sku100def_every_2026-11-16.csv"

CSV tag `sku100def`. Controls: `sku100n16fix` (2026-11-15, the knob build,
lane on) and `sku100n16fixoff` (lane off).
