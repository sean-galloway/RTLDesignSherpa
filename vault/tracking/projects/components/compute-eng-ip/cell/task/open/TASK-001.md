# TASK-001: Cell slice 2 — cell_credit + cell_packetizer + strap counter

**Priority:** P1
**Status:** open -- 2026-10-19
**Owner:** sean galloway

## Why

Slice 1 (fill path: cell_top, cell_rx, cell_cfg_regs, cell_mem_in,
cell_mem_out) is built and green. Slice 2 is the next rung of the cell
ladder: the credit loop and the result packetizer. Specified in cell MAS
v0.12 ch04 (02_credit_logic.md, 03_packetizer_and_exec.md).

## What

Per MAS v0.12 ch04:

- `cell_credit`: per-source `owed` counters (source coordinate stored per
  input-memory line), `CREDIT_BATCH_N` batching (default 1), 64-cycle
  partial-batch timeout, boot `credit`/`set` advertisement (IN_DEPTH flits,
  to level=3). Credit packets are credit-class 0 (sink space) — target
  address bits [1:0] per TILE_SPEC 11.5 (added to the MAS 2026-10-19).
- `cell_packetizer`: batch result flits up to `EMIT_BATCH_X` (default 4),
  flush on batch-full or CTRL.flush-and-send, build write-format packets
  with the 11.5 tile header, destination/tag from FLUSH_DEST/FLUSH_TAG
  (0x54/0x58), strap check (`TILE_LAND_FLITS` counter covers header +
  payload) before tvalid.
- Two-header beat-chained demux parse per TILE_SPEC 11.6 (supersedes the
  provisional slice-1 64-bit TUSER packing).
- Rename the slice-1 RTL grant identifiers to strap terms while the surface
  is small: `STATUS_GRANT_NONZERO_BIT` -> `STATUS_STRAP_NONZERO_BIT`,
  `IRQ_GRANT_STARVED_BIT` -> `IRQ_STRAP_STARVED_BIT` (cell_pkg.sv,
  cell_cfg_regs.sv, cell_top.sv, dv/tests/test_cell.py). Docs moved to strap
  terms 2026-10-19 and currently carry RTL-alias notes for these names.

## Done when

cell_credit + cell_packetizer RTL in `cell/rtl/`, func+gate green in the
cell DV suite, credits observed returning to the recorded source coordinate
in simulation, MAS status lines move to built.

## Notes

Blocked-on: nothing in the cell; the rapids side of straps is rapids
TASK-027 territory (TILE_SPEC 11.9) — the cell half can land standalone.
