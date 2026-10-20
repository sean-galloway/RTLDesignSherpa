# TASK-002: Milestone M1 — fully working tetrad on the FPGA

**Priority:** P1
**Status:** open -- 2026-10-19
**Owner:** sean galloway

## Why

Owner direction 2026-10-19: the milestone ladder (TILE_SPEC 12). M1 is the
first rung: 4 cells + the gatling sequencer over delta, on the FPGA. It
proves the cell datapath, the credit loop, and programmability end-to-end
at the smallest useful scale.

## Done when

A tetrad runs a real cell program on the Genesys2: in-band cfg + mem fill,
compute through the alu-infer pipeline, credit returns observed, result
drain via straps — against a golden model.

## Notes

Depends on cell TASK-001/002 (slices 2-3) and the gatling RTL (gatling
TASK-002). Feeds alu-infer TASK-007 (M-item sweep happens here).
