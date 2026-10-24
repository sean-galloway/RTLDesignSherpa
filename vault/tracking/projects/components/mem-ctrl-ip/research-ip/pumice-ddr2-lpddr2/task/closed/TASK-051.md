# TASK-051: the pick core reads the command payload by slot -- records carry no row / column

> Source: the measurement in report 5.11 (TASK-050): both storage backends
> spent most of their LUTs materialising row + column in 32 head records per
> cycle, and the owner's standing goal is granite's area against LiteDRAM.
> Related: TASK-050 (the FIFO store this lands on), recovery plan section
> 2.4 (the plane contract).

**Priority:** P2
**Status:** closed 2026-10-24 (board +0.194 ns, 0 failing endpoints; granite_core 7 403 -> 6 634 LUT, 5 316 -> 4 580 FF; store 3 894 -> 3 096 LUT)
**Owner:** TBD

## What landed

- `mc_bank_pick`: new inputs `wr_slot_row_i` / `wr_slot_col_i` /
  `rd_slot_row_i` / `rd_slot_col_i` (the backend's slot fields, flat
  N x ROW / N x COL); the fire payload selects row and column by the
  winner's slot (`w_sel_slot`, from the registered winner pair) instead of
  reading them off the head record. The record's row / col fields are no
  longer read by this core.
- `mc_scheduler_plane`: the BANK_PICK branch feeds the picker from the
  existing `*_sch_row_i` / `*_sch_col_i` vectors (the entry store already
  drove them; the FIFO store now does).
- `mc_bank_fifo_store`: outputs `wr_sch_row_o` / `wr_sch_col_o` /
  `rd_sch_row_o` / `rd_sch_col_o` (its slot registers, no mux); the records
  carry vld, slot, behind flags, hit and the age flag only.
- `granite_core` FIFO branch and the contract tb_top wire the slot fields
  through; `mc_common_pkg` documents the record's row / col as unread by the
  pick core.

## Measured

| | before (TASK-050 shipped) | after |
|---|---|---|
| granite_core LUT / FF | 7 403 / 5 316 | 6 634 / 4 580 |
| mc_bank_fifo_store LUT / FF | 3 894 / 2 826 | 3 096 / 2 090 |
| WNS at 75 MHz | +0.304 (+0.545 rebuilt) | +0.194 ns, 0 / 109 413 |
| perf, 8 threads std families | 556.9 / 555.3, 557.6 / 557.2, 533.5 / 525.9, 459.0 / 457.7 | identical to the decimal |
| perf, mixed 8 threads | 98.1, 200 290 / 200 299 cycles | identical |

## Gates

contract battery 12 / 3 strict xfailed (entry + fifo cells); granite suite
6 / 1 xfailed on the FIFO store and on the entry store; pumice
`run-all-func-both` 218 / 218 both geometries (shared plane); lint of
granite_core both backends and pumice_core both cores (0 errors); the
contract tb_top's direct `mc_bank_pick` instance gained the four pins (the
non-fatal lint let a PINMISSING through once -- the battery caught it).
Built text == committed text by md5 (report 5.11, row 7).
