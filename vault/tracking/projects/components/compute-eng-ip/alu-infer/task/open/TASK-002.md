# TASK-002: PWL/LUT activation row (sigmoid/tanh/gelu/exp)

**Priority:** P2
**Status:** open -- 2026-10-19
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
