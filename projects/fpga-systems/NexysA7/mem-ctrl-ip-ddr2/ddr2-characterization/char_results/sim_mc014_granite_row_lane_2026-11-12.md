# Granite with a row lane on the bank-pick core, sim at the sku100 point (memory-controllers MC-014, 2026-11-12)

The 2026-11-12 measurement (`sim_mc013_command_slot_dual_issue_2026-11-12.md`)
named the one DRAM command per MC cycle as granite's ceiling on the
bank-parallel miss families. This is the same proxy with the fix built: a
second, row-only issue lane on `mc_bank_pick` (`DUAL_ISSUE`), the plane's
`a2_*` connected for the BANK_PICK core, the word through `mc_dfi_2p1_plane`
on `DFI_PHASE.row_phase`, and two new granite CSR fields
(`SCHED_POLICY.dual_issue`, `DFI_PHASE.row_phase`). Same point as before:
granite perf proxy, 100 MHz MC / CK 200 (DDR2-400, peak 800 MB/s), DFI 1:2,
x16 BL4, `t_phy_wrlat` 1, tREFI 772, TEST_TXN 1024, `TEST_DUAL=1` with
`row_phase` 1. Cells are write / read MB/s over the board timer's window
(first beat in to last response out).

| family (bl8) | granite lane OFF, same RTL (control) | granite lane ON | board 2026-11-09 (lane off) | model ideal (open32) | model 2 CK (open32_mc2) | pumice lane ON (11-12) | granite ON / ideal |
|---|---|---|---|---|---|---|---|
| col_major_interleaved | 681 / 686 | **686 / 773** | 684 / 686 | 781 / 782 | 780 / 781 | 682 / 767 | 0.88 / 0.99 |
| row_thrash (4 gen) | 684 / 687 | **687 / 775** | 688 / 688 | 779 / 743 | 779 / 781 | 683 / 769 | 0.88 / 0.99 |
| random (4 gen) | 626 / 656 (11-12) | **627 / 722** | 635 / 661 | 767 / 760 | 770 / 773 | 623 / 703 | 0.82 / 0.93 |
| col_major (control) | 413 / 517 (11-12) | 414 / 516 | 416 / 520 | 465 / 570 | 418 / 521 | 410 / 472 | timer-bound, unchanged |

Every run passed with 0 mismatched beats and no bank-state violation at the
DRAM model (`no_act_before_rd/wr`, `act_on_active_bank`, `ref_with_open_row`,
`ap_on_idle_bank`; the model's unit-less soft timing counters are not a check,
see the proxy). The lane-off control on the new RTL is cycle-identical to the
2026-11-12 cells on `col_major_interleaved` (9 619 / 9 558 cycles, the same
soft counters to the unit) and within 3 read cycles in 38 165 on `row_thrash`.

## What the command trace says (lane ON)

The probe logs the plane's `evt_*` strobes (the main slot) and, from this
change on, the lane's `a2_act` / `a2_pre` as ACT2 / PRE2; the slot statistic
counts a cycle once (one word).

- `col_major_interleaved`: the main slot carried 33 ACTs where it carried
  2 085 before -- 98.4 percent of the row commands rode the lane. Reads are
  a pure column stream (RD gap 1 in 8 163 of 8 192, where the lane-off control
  has 1 039 gaps of 2 -- one per burst, the ACT's slot); the read cell moves
  686 -> 773, 1 percent under the ideal. Main-slot occupancy in the busy bins
  0.965 -> 0.914.
- `row_thrash`: 118 of 8 338 ACTs on the main slot, RD gap 1 in 32 650 of
  32 768; 687 -> 775 reads; occupancy 0.970 -> 0.912.
- `random`: 6 736 of 8 167 ACTs (82 percent) and 520 of 754 PREs rode the
  lane; 656 -> 722 reads; occupancy 0.909 -> 0.863. The rest of its gap to
  the ideal is the family's same-bank row switches (524 RD gaps of 5 and 524
  WR gaps of 8: RD -> PRE/ACT -> RD on one bank, the timer-bound hop the
  model's 2 CK column also pays), not the slot.
- `col_major`: 2 081 ACTs, all on the main slot (one bank, nothing to ride
  beside), the same 12 / 15 ACT period as before. The lane changes nothing,
  as it should not.

## The writes did not move -- MC-015

With the lane on, the write cells stay at 686 / 687 against reads of 773 /
775. The write stream has the same shape with and without the lane: seven WRs
a cycle apart, then a gap of 2, per 8-beat AXI burst (1 009 gaps of 2 in
1 024 bursts on `col_major_interleaved`, 4 045 in 4 096 on `row_thrash`), so
the ACT that took a slot per burst was hiding behind a bubble the write path
already paid. Pumice shows the same one cycle per burst with its lane
(682 / 767). The bubble sits between the last beat of one AXI write burst and
the first of the next -- the intake or the injector, not the scheduler. Filed
as memory-controllers MC-015 with the trace evidence.

## Method and recipe

- The lane is bit-identical off: the `equiv` / `equiv_n4` tasks in
  `formal/mc_common/mc_bank_pick` (20-cycle lockstep against the golden copy
  on free inputs) still pass with the lane's code present at `DUAL_ISSUE = 0`;
  the new `dual` task proves the lane's word invariants at `DUAL_ISSUE = 1`
  (one row command per word, only beside a column or alone, never the main
  winner's bank, the live gate re-checked); `dual_cover` reaches both classes
  beside a column and alone.
- Regressions on the shared RTL: granite top (25 passed, 5 skipped, 1 xfailed,
  the standing marks), pumice fub / macro / top / phy (220 + 32 passed), the
  common-ip store-arbiter contract bench (the direct `mc_bank_pick`
  instantiation).
- Recipe (from the char framework's `dv/tests`):
  `TEST_FPGA_CLK_HZ=100000000 TEST_T_PHY_WRLAT=1 TEST_TREFI=772 TEST_TXN=1024
  TEST_LEVEL=FUNC TEST_DUAL=1 PERF_CMD_TRACE=1 TEST_FAMILIES=<fam>
  TEST_NUM_GEN=<1|4> PERF_DUMP=<path>.json pytest
  test_granite_char_perf.py::test_granite_char_perf`; the `.gaps.json` beside
  the dump carries the per-kind gap histograms and the slot occupancy.
  `TEST_DUAL=1` builds its own `sim_build` tag (`_dual`).

Next: the board. A sys100 build with `DUAL_ISSUE = 1`, timing (the pick's
select cone grows by the lane's "a row can ride" term; the fire cone by one
AND and the lane's own gate), then the char `every` + `windows` suites with
`dual_issue` on and `row_phase` 1.
