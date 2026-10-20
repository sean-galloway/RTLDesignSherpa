# TASK-002: PWL/LUT activation row (sigmoid/tanh/gelu/exp)

**Priority:** P2
**Status:** closed -- 2026-10-20
**Owner:** sean galloway

## Why

Owner ruling 2026-10-19 (architecture review): relu is the only activation
in v1. Sigmoid/tanh/gelu/exp are transcendentals — the standard accelerator
answer in bf16 hardware is a piecewise-linear / LUT approximation, not a
true transcendental unit. exp in particular is the missing half of softmax
(with the reduce row, TASK-001, and reciprocal-multiply for the divide — no
true divider is planned).

## What

Add a PWL/LUT activation row (PRD v0.50 §3 roadmap, 2026-10-19 addendum):
256-entry LUT with linear interpolation, sub-op selects the function
(sigmoid / tanh / gelu / exp / ...). LUT contents are config-loaded in-band
like everything else in the cell. bf16 in, bf16 out, RNE at presentation,
matching the library rounding policy.

## Done when

Row is in the alu-infer MAS and RTL with loadable LUT contents, func+gate
green, accuracy characterized against a golden fp32 model over the bf16
input range (error bound recorded in the MAS).

## Notes

Good learning payload on its own: LUT sizing vs interpolation error is a
clean design study. Sequenced after v1 FPGA bring-up.

## Closed 2026-10-20

OP_PWL (9) + OP_PWL_LUT (10): 256-entry {slope, intercept} LUT loaded in-band through the seam, log-spaced segments, bf16(fma(slope, x, icpt)). Table builder + bit-level model: alu-infer/bin/alu_infer_pwl.py (modeled max abs error sigmoid 3.8e-3, tanh 3.3e-3, gelu 8.2e-3, silu 1.6e-2; exp 2.9e-2 rel on [-16, 4]). Test `pwl`: load, read-back, bit-exact evaluation, accuracy bound.

Verified: gate (82 cells) and func (184 cells, COVERAGE=1) through the area Makefile, four build configs (default, deep, flat, lean); testplan 25/25 scenarios VERIFIED (--strict). MAS 0.50 reconciled. Sequenced ahead of FPGA bring-up at the owner's request ("implement all of the features in the ALU-infer MAS AND PRD", 2026-10-20).
