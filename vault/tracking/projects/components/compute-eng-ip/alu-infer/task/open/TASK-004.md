# TASK-004: int8 x4-lane element width (func_sel[8:7], open item M6)

**Priority:** P2
**Status:** open -- 2026-10-19
**Owner:** sean galloway

## Why

Owner ruling 2026-10-19 (architecture review): the format roadmap runs
through the reserved `func_sel[8:7]` element-width field (open item M6) —
one ALU per cell, wider format coverage, no A/B/C fork. int8 is the first
extension: edge inference standardized on int8 (Jacob et al., CVPR 2018),
the same line width carries 4 lanes = 4 MACs/clk per cell, and it teaches
quantization. bf16 stays the v1 format.

## What

Add an int8 element mode to alu-infer: 4 lanes per 32-bit line, int8
multiply with int32 accumulate in the MAC row (exactly analogous to the
bf16->fp32 exactness argument: 8+8 significand bits << 31), add/sub/mul/
min/max/compare rows widened to 4 lanes. Element width is sampled at issue
from `func_sel[8:7]`; gatling reads the mode via `CFG[0]`.

## Done when

int8 mode is in the alu-infer MAS and RTL, func+gate green; the same cell
program runs a quantized layer end-to-end; M6 is closed in the MAS open
items.

## Notes

Depends on TASK-006 (tag alignment) only if row depths diverge per format —
check at design time. After v1 FPGA bring-up.
