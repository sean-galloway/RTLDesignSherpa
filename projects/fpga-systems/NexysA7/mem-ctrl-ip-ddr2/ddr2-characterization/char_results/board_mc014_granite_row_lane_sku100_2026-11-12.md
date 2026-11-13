# Granite's row lane on the Nexys A7 at 100 MHz: five builds to a design point, then the board (memory-controllers MC-014 board half, 2026-11-12)

The sim half (`sim_mc014_granite_row_lane_2026-11-12.md`) built the lane and
put granite's bank-parallel miss reads within 1 percent of the model's ideal.
This is the board half: the sys100 FPGA SKU with `DUAL_ISSUE` built
(`GRANITE_DUAL_ISSUE=1 GRANITE_SYS_100=1 make bitstream` in
`targets/granite`), timing under the 0.2 ns clock-uncertainty budget the board
XDCs carry (MC-011), then the char `every` + `windows` suites with the lane on
(`TEST_DUAL_ISSUE=1`: `SCHED_POLICY.dual_issue` + `DFI_PHASE.row_phase` 1) and,
on the same bitstream, off. Reference: the lane-less sku100 bitstream of
2026-11-09 (+0.147 ns, 35 727 LUT).

## Timing: the lane as first built did not fit, four register-only cuts made it fit

| build | lane RTL | LUT | WNS (ns, under the 0.2 ns budget) | failing endpoints | where |
|---|---|---|---|---|---|
| 1 | as simulated in the morning | 36 587 | -1.715 | 462 | lane pick (15-18 levels, 68 % route), DFI formatter address, then collateral everywhere |
| 2 | cut 1 + cut 2 | 36 333 | -0.549 | 29 | 26 in the lane pick: the registered main winner's bank compare |
| 3 | + cut 3 | 36 286 | -0.105 | 9 | 5 lane pick: the store's "column can issue now" input; 4 page-policy (noise band) |
| 4 | + cut 4 | -- | killed | -- | the mixed sim showed the hold deadlock before the build finished |
| 5 | + cut 4 + the hold rule | 36 345 | **+0.059** | **0** | worst path is the main pick (`r_req` -> `r_win_cls`), the pre-lane critical path |

The cuts, each the same mistake in a smaller form -- a lane term read from
something the main lane also computes or waits on:

1. **No same-cycle exclusion of the main select's fresh row pick.** The lane's
   rotor ran after the main select cone (`w_sel_src` -> `w_oh_row`). The
   fire stage's clash term (the REGISTERED main winner's bank) already blocks
   a lane fire to that bank; the two lanes may now load one pair and the lane
   re-picks a cycle later. A fresh main row pick only happens when no column
   can fire -- a cycle the lane could not use anyway.
2. **The lane fires beside a main COLUMN only, never into an idle main slot**,
   and the plane keeps its `a2_*` out of the push valid for the pick core
   (the FR-FCFS core's lane may fire alone, so for that core they stay in).
   With them in, the lane gate -- a function of the main fire -- sat on the
   command-valid cone into the DFI path: -1.49 ns on the formatter's address.
   The formal `dual` task's `a_beside_col` is now "beside a column", not
   "beside a column or alone"; the two `c_*_alone` covers became
   ACT-beside-RD / ACT-beside-WR.
3. **The candidate set no longer excludes the registered main winner's bank**
   (sixteen compares against `r_win_pair`); the clash term at the fire does
   that job.
4. **"A bank is busy" means a column request is PENDING there, ready or not**;
   the lane no longer reads the store's `wr_commit_ready_now_i` /
   `rd_issue_ready_i`. A bank whose column merely waits for its data is still
   not one to re-open from the lane.

And one consequence the formal task could not see (it proves fire invariants,
not liveness): after cut 2 a HELD lane pair, stale-masked from the main select
for its life in the lane, had no way out when no column was available -- the
main could not take it, the lane could not fire it, and the row waited for a
refresh. `mixed` in sim fell to 16 / 16 MB/s with every beat correct, and the
board on build 3 showed the same 16 / 16 (below). The hold rule became: a held
pair is masked only while a column request is pending somewhere; with nothing
pending the main select takes it as its own row pick and the clash makes the
lane re-pick.

## Sim after the cuts (sku100 point, TEST_TXN 1024, final RTL)

| family (bl8) | lane OFF (control) | lane ON, morning RTL | lane ON, final RTL |
|---|---|---|---|
| col_major_interleaved | 681 / 686 | 686 / 773 | 686 / 774 |
| row_thrash (4 gen) | 684 / 687 | 687 / 775 | 687 / 773 |
| random (4 gen) | 626 / 656 | 627 / 722 | 627 / 721 |
| mixed (4 + 4 gen) | 262 / 331, union 524 | not run | 475 / 300, union **601** |

Zero mismatched beats. `mixed` gains 15 percent on the union window (the
direction share moves: the writers finish first). Build 3's RTL, for the
record: mixed 16 / 16, random 624 / 706. Formal on the final RTL: `equiv`,
`equiv_n4`, `cover`, `dual`, `dual_cover` all PASS, every cover reached.
Regressions on the final RTL: granite top 25 passed / 5 skipped / 1 xfailed,
pumice 220 + 32 passed, ddr2_char_framework and the store-arbiter contract
bench below.

## Board, build 5 (WNS +0.059, the design point)

### every (68 lane-on cells, 68 lane-off cells on the lane bitstream; mismatched beats: 0)

| scenario | preset | 2026-11-09 (no lane built) | lane built, OFF | lane ON | reads ON / OFF |
|---|---|---|---|---|---|
| col_major_bl16 | defaults | 541 / 623 | 541 / 623 | 541 / 623 | 1.00x |
| col_major_bl16 | open_page | 541 / 623 | 541 / 623 | 541 / 623 | 1.00x |
| col_major_bl4 | defaults | 283 / 389 | 283 / 389 | 283 / 389 | 1.00x |
| col_major_bl4 | open_page | 283 / 389 | 283 / 389 | 283 / 389 | 1.00x |
| col_major_bl8 | defaults | 416 / 520 | 416 / 520 | 416 / 520 | 1.00x |
| col_major_bl8 | open_page | 416 / 520 | 416 / 520 | 416 / 520 | 1.00x |
| col_major_bl8_gap | defaults | 376 / 400 | 376 / 400 | 376 / 400 | 1.00x |
| col_major_bl8_gap | open_page | 376 / 400 | 376 / 400 | 376 / 400 | 1.00x |
| col_major_bl8_multiid | defaults | 416 / 520 | 416 / 520 | 416 / 520 | 1.00x |
| col_major_bl8_multiid | open_page | 416 / 520 | 416 / 520 | 416 / 520 | 1.00x |
| col_major_interleaved_bl16 | defaults | 721 / 729 | 721 / 729 | 729 / 776 | 1.06x |
| col_major_interleaved_bl16 | open_page | 729 / 730 | 729 / 730 | 729 / 776 | 1.06x |
| col_major_interleaved_bl4 | defaults | 617 / 615 | 617 / 618 | 688 / 770 | 1.25x |
| col_major_interleaved_bl4 | open_page | 615 / 619 | 615 / 619 | 688 / 774 | 1.25x |
| col_major_interleaved_bl8 | defaults | 684 / 686 | 684 / 686 | 688 / 774 | 1.13x |
| col_major_interleaved_bl8 | open_page | 688 / 688 | 688 / 688 | 688 / 774 | 1.12x |
| col_major_interleaved_bl8_multiid | defaults | 684 / 688 | 684 / 686 | 688 / 774 | 1.13x |
| col_major_interleaved_bl8_multiid | open_page | 688 / 688 | 688 / 688 | 688 / 774 | 1.12x |
| incremental_bl16 | defaults | 772 / 773 | 772 / 773 | 772 / 776 | 1.00x |
| incremental_bl16 | open_page | 772 / 775 | 772 / 775 | 772 / 778 | 1.00x |
| incremental_bl4 | defaults | 772 / 773 | 772 / 773 | 772 / 776 | 1.00x |
| incremental_bl4 | open_page | 772 / 775 | 772 / 775 | 772 / 778 | 1.00x |
| incremental_bl8 | defaults | 772 / 773 | 772 / 773 | 772 / 776 | 1.00x |
| incremental_bl8 | open_page | 772 / 775 | 772 / 775 | 772 / 778 | 1.00x |
| incremental_bl8_multiid | defaults | 772 / 773 | 772 / 773 | 772 / 776 | 1.00x |
| incremental_bl8_multiid | open_page | 772 / 775 | 772 / 775 | 772 / 778 | 1.00x |
| row_major_bl16 | defaults | 775 / 778 | 775 / 778 | 775 / 778 | 1.00x |
| row_major_bl16 | open_page | 775 / 778 | 775 / 778 | 775 / 778 | 1.00x |
| row_major_bl4 | defaults | 775 / 778 | 775 / 778 | 775 / 778 | 1.00x |
| row_major_bl4 | open_page | 775 / 778 | 775 / 778 | 775 / 778 | 1.00x |
| row_major_bl8 | defaults | 775 / 778 | 775 / 778 | 775 / 778 | 1.00x |
| row_major_bl8 | open_page | 775 / 778 | 775 / 778 | 775 / 778 | 1.00x |
| row_major_bl8_multiid | defaults | 775 / 778 | 775 / 778 | 775 / 778 | 1.00x |
| row_major_bl8_multiid | open_page | 775 / 778 | 775 / 778 | 775 / 778 | 1.00x |

### windows (9 lane-on cells, 9 lane-off cells on the lane bitstream; mismatched beats: 0)

| scenario | preset | 2026-11-09 (no lane built) | lane built, OFF | lane ON | reads ON / OFF |
|---|---|---|---|---|---|
| mixed_bl8 | close_page | 48 / 48 | 48 / 48 | 69 / 115 | 2.40x |
| mixed_bl8 | defaults | 251 / 283 | 260 / 319 | 487 / 300 | 0.94x |
| mixed_bl8 | open_page | 263 / 330 | 262 / 330 | 334 / 649 | 1.97x |
| random_bl8 | close_page | 149 / 190 | 149 / 190 | 149 / 184 | 0.96x |
| random_bl8 | defaults | 628 / 657 | 628 / 658 | 629 / 723 | 1.10x |
| random_bl8 | open_page | 635 / 661 | 635 / 661 | 635 / 729 | 1.10x |
| row_thrash_bl8 | close_page | 175 / 229 | 175 / 229 | 170 / 229 | 1.00x |
| row_thrash_bl8 | defaults | 688 / 688 | 684 / 688 | 688 / 774 | 1.12x |
| row_thrash_bl8 | open_page | 688 / 688 | 688 / 688 | 688 / 774 | 1.13x |

Smoke (init + write_read + memtest 32 / 32) passes lane off and lane on. The
lane-OFF cells on this bitstream match the 2026-11-09 lane-less bitstream on
every cell (the two `mixed defaults` cells differ by the run-to-run state the
TASK-003 note describes; everything else is within rounding). With the lane
ON, every bank-parallel miss cell moves and nothing else does:

- `col_major_interleaved`: reads 686 -> 774 at bl8 (+13 %), 615 -> 770 / 774
  at bl4 (+25 %, where the ACT was one of five commands per burst), 729 -> 776
  at bl16 (+6 %); the model's best policy is 782. Writes: 684 -> 688, the
  MC-015 bubble.
- `row_thrash`: 688 -> 774 reads (+13 %), writes 688.
- `random`: 657 / 661 -> 723 / 729 reads (+10 %), writes unchanged; the model
  gives 772-780 for the best policy, the remainder is same-bank row switches.
- `mixed`: both directions rise and the share between them moves with the
  preset -- defaults 251 / 283 -> 487 / 300 (the writers finish first),
  open_page 263 / 330 -> 334 / 649 (the readers do). The union is what the
  lane buys here; the sim's union went 524 -> 601.
- `incremental`, `row_major`, `col_major`, the half-burst and threaded
  profiles' cousins in `every`: identical to the lane-less cells (the lane
  has no row command to carry on a row-hit stream, and `col_major` is
  timer-bound in one bank).


## The two preview bitstreams

Both preview bitstreams ran the full `every` + `windows` suites lane on and
off with 162 cells each and zero mismatched beats, and their lane-OFF cells
match the 2026-11-09 reference within 0.52 percent on every one of 136 cells:
a bitstream that misses timing by 1.7 ns on the speed file still works on this
part at room temperature, which is exactly why the budget is a rule and not a
measurement.

- Build 1 (-1.715 ns, the morning lane): `col_major_interleaved_bl8` 688 / 776,
  `_bl4` 688 / 770 (from 617 / 615), `_bl16` 729 / 776, `row_thrash` 688 / 776,
  `random` 635 / 730, `mixed` 333 / 627 (from 263 / 330). The lane's number
  before any cut.
- Build 3 (-0.105 ns, cuts 1-3, the hold deadlock in): `mixed` **16 / 16** on
  both presets, `random` open_page 528 / 729, `row_thrash` defaults 656 / 774
  -- the sim's deadlock, on silicon, to the MB/s.

## Recipe

    cd projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/targets/granite
    GRANITE_SYS_100=1 GRANITE_DUAL_ISSUE=1 make bitstream      # reports -> fpga/reports, bitstream fpga/bitstream/ddr2_char.bit
    make program BITSTREAM=fpga/bitstream/ddr2_char_granite_sku100_dual5_2026-11-12.bit
    make run SEQUENCES="init write_read memtest" RUN_ARGS="--controller granite"                       # smoke, lane off
    TEST_DUAL_ISSUE=1 make run SEQUENCES="init write_read memtest" RUN_ARGS="--controller granite"     # smoke, lane on
    TEST_DUAL_ISSUE=1 make run SEQUENCES="init char" RUN_ARGS="--controller granite --profile every --txn-scale 4000 --char-csv <char_results>/char_granite_sku100dual5_every_2026-11-12.csv"
    make run SEQUENCES="init char" RUN_ARGS="--controller granite --profile every --txn-scale 4000 --char-csv <char_results>/char_granite_sku100dual5off_every_2026-11-12.csv"

CSV tags: `sku100dual5` (lane on) and `sku100dual5off` (lane off) for the
design point; `sku100dual` / `sku100dualoff` (build 1) and `sku100dual3` /
`sku100dual3off` (build 3) for the previews. Reports:
`targets/granite/fpga/reports_sys100_mc014_dual{,2,3,5}_2026-11-12`.
