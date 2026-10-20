# TASK-005: fp32 single-lane element width (func_sel[8:7], open item M6)

**Priority:** P3
**Status:** open -- 2026-10-19
**Owner:** sean galloway

## Why

Owner ruling 2026-10-19 (architecture review): fp32 mode (one lane per
32-bit line) turns the tile into a general vector engine for workloads
beyond inference — signal processing, norms, anything that wants real
mantissa width. Second format extension after int8 (TASK-004).

## What

Add an fp32 element mode to alu-infer: 1 lane per line, fp32 add/sub/mul/
min/max/compare and an fp32 MAC (fp32 x fp32 product is NOT exact in fp32 —
record the rounding policy; consider a wider internal accumulator only if
the latency budget allows). Element width sampled at issue from
`func_sel[8:7]`.

## Done when

fp32 mode is in the alu-infer MAS and RTL, func+gate green; MAC rounding
policy recorded in the MAS; M6 closed together with TASK-004.

## Notes

Lowest priority of the roadmap items — bf16+int8 cover the accelerator
story; fp32 is the "compute vehicle" stretch.
