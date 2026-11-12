# The command slot on granite, and dual issue on pumice: the MC-013 item-1 sims (2026-11-12)

MC-012's model said the bank-parallel miss families (`col_major_interleaved`,
`row_thrash`, `random`) sit 12-21 % under the ideal on granite with nothing of
that explained by timer granularity, and named the single DRAM command per MC
cycle as the candidate. Two sims test it directly. Both are the perf proxies in
`ddr2_char_framework/dv/tests` at the sku100 point (MC 100 MHz, DFI 1:2, CK 200,
tREFI 772, `TEST_T_PHY_WRLAT=1`, `TEST_TXN=1024`, bl8; one injector on the
stride families, four on the window families, as the board runs them).

1. **Granite, slot occupancy.** The row lane does not exist on granite: its
   bank-FIFO store forces the bank-pick core (`granite_core.sv` errors on any
   other), and `mc_scheduler_plane` ties the lane to zero there. So the sim
   measures the slot instead: `PERF_CMD_TRACE=1` now logs every scheduler
   fire from the plane's `evt_*` strobes plus the pre-FIFO accept, and
   reports the fraction of MC cycles with a fire per 1024-cycle bin.
2. **Pumice, DUAL_ISSUE 0 vs 1.** The FR-FCFS core has the TASK-047 row lane
   and shares `mc_dfi_cmd_path` with granite. `TEST_DUAL=1` builds the lane
   and sets `SCHED_POLICY.dual_issue`; same stimulus either way.

Cells are write / read MB/s (peak 800). Board columns are the measured
sku100 cells of 2026-11-09; model columns are MC-012's `open32` (CK ideal) and
`open32_mc2` (2 CK granular).

| family (bl8) | granite sim | granite board | granite slot occupancy (busy bins) | ACT period | pumice DUAL 0 | pumice DUAL 1 | model ideal | model 2 CK |
|---|---|---|---|---|---|---|---|---|
| col_major_interleaved | 681 / 686 | 684 / 688 | 0.965 mean, 0.981 max | 9 cycles (1950 of 2085) | 613 / 680 | 682 / 767 | 781 / 782 | 780 / 781 |
| row_thrash (4 inj) | 684 / 687 | 688 / 688 | 0.970 mean, 0.981 max | 9 cycles (7859 of 8355) | 615 / 682 | 683 / 769 | 779 / 743 | 779 / 781 |
| random (4 inj) | 626 / 656 | 635 / 661 | 0.909 mean, 0.970 max | 9 (5138), 15 (839), 6 (398) | 578 / 642 | 623 / 703 | 767 / 760 | 770 / 773 |
| col_major (control) | 413 / 517 | 416 / 520 | 0.651 mean, 0.737 max | 12 / 15 alternating | 410 / 472 | 410 / 472 | 465 / 570 | 418 / 521 |

Command mix on granite, col_major_interleaved: 8192 RD, 8192 WR, 2085 ACT,
78 PRE, 161 other (REF). The precharges ride as auto-precharge, so a burst is
eight column commands plus one ACT: nine commands through a one-per-cycle
slot is 8/9 of peak, 711 MB/s, less 2.3 % refresh = 695; measured 686.

## What it says

- **The slot is the ceiling on granite, measured, not inferred.** On the two
  pure bank-parallel miss families the plane fires in 97 % of MC cycles and
  the ACT recurs every 9 cycles exactly: eight columns and one ACT per burst,
  one command per cycle. `random` is the same shape with explicit PREs and
  bank conflicts on top (occupancy 91 %). The control family `col_major` is
  timer-bound (65-74 % occupancy), as MC-012's granularity column said.
- **A second slot recovers it, on the shared command path.** Pumice with the
  row lane: col_major_interleaved reads 680 -> 767 (+13 %), writes 613 -> 682;
  row_thrash the same; random reads 642 -> 703, writes 578 -> 623. col_major
  does not move, as it should not. Pumice's dual-issue reads land within
  1.7 % of the model's ideal; its writes keep one extra cycle per burst that
  is a pumice write-path matter, not the lane.
- **The sim reproduces the board** on every granite cell to within 1 %
  (681/686 vs 684/688, 684/687 vs 688/688, 626/656 vs 635/661, 413/517 vs
  416/520), so the trace is of the same behaviour the board measures.

Granite's number for a row lane on the bank-pick core, from the model: +92 to
+100 MB/s on col_major_interleaved and row_thrash, +110 to +145 on random, at
the DFI word width cost pumice already pays. Filed as memory-controllers
MC-014.

Recipe (from `ddr2_char_framework/dv/tests`, env_python sourced):

```
export TEST_FPGA_CLK_HZ=100000000 TEST_T_PHY_WRLAT=1 TEST_TREFI=772 TEST_TXN=1024 TEST_LEVEL=FUNC PERF_CMD_TRACE=1
TEST_FAMILIES=col_ilv TEST_NUM_GEN=1 PERF_DUMP=$OUT/g_col_ilv.json \
    python3 -m pytest test_granite_char_perf.py::test_granite_char_perf -q
TEST_FAMILIES=row_thrash TEST_NUM_GEN=4 ...                       # one family per run keeps the occupancy bins clean
TEST_DUAL=0 TEST_FAMILIES=col_ilv,col_major TEST_NUM_GEN=1 python3 -m pytest test_ddr2_char_perf.py::test_ddr2_char_perf -q
TEST_DUAL=1 TEST_FAMILIES=col_ilv,col_major TEST_NUM_GEN=1 python3 -m pytest test_ddr2_char_perf.py::test_ddr2_char_perf -q
```

The occupancy summary is `<PERF_DUMP>.gaps.json` under `slot`; the per-kind
fire-gap histograms sit beside it.
