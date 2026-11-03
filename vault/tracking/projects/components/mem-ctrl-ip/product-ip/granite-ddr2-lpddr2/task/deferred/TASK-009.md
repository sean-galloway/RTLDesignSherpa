---
title: TASK-009 — DFI 1:4 board point, first DQ word of a read run sampled early
summary: On the 1:4 (nphases 4) Nexys bitstream the first device word of every read run is wrong on w_dfi_rddata, ahead of the controller; four board experiments listed, parked until 1:4 is a product point.
---

# TASK-009 — DFI 1:4 board point, first DQ word of a read run sampled early

**State:** deferred · **Area:** product-ip/granite-ddr2-lpddr2 · **Opened:** 2026-11-02
**Status:** deferred 2026-11-02 -- pending the DFI 1:4 build becoming a
product point (the shipped boards are DFI 1:2 at 75 and 100 MHz, both clean).
**Parent:** TASK-003 item 6 (closed 2026-11-02); evidence in its log,
"2026-10-29 evening, item 6: both residuals read off the bus".

## What

On the 1:4 128-bit bitstream (`board75_dfi4ila`, BL8, x16, CK 300) the best
leveling cells give 1 wrong word in 8 per read RUN: an ILA on the DFI
boundary shows word 0's lowest device word as the undriven bus (0x2fff for
0x1db6) on `w_dfi_rddata`, before the harness delay line; words 1..7 sit
inside a wide eye (taps 14..30). The controller, aligner and return path
carry exactly what the PHY gives them. The 1:2 points do not show it.

## Experiments, in order (all board-side)

1. DRAM output drive and ODT via an EMRS1 override (full vs reduced drive,
   RTT off / 75 / 150).
2. FPGA-side DQ termination (`IN_TERM UNTUNED_SPLIT_50`) against a first bit
   that starts from high-Z.
3. A first-word-aware leveling pattern.
4. The `a7ddrphy_nph4` read path's bitslip / rdphase pairing (one phase = two
   bitslips: the first-word position is quantised to half a word).

## Done when

The 1:4 bitstream reads every word of a run correctly at a leveled cell, or
the defect is attributed to the board and the 1:4 point is declared not
supported on the Nexys A7.
