# TASK-005: Milestone M4 — rapids + tile on real data and benchmarks

**Priority:** P1
**Status:** open -- 2026-10-19
**Owner:** sean galloway

## Why

Owner direction 2026-10-19: the top of the ladder (TILE_SPEC 12). Real
workloads, real numbers: the tile computes actual inference data through
rapids and produces benchmark results worth charting.

## Done when

A real network layer (or better) runs rapids -> tile -> rapids on the FPGA
against a golden model, with performance numbers recorded in the docs
(tokens/cycle, fabric utilization, ALU row latencies — the M8 latency table
lands here if it hasn't already).

## Notes

Depends on M3 (TASK-004). This is where the alu-infer function-set roadmap
(reduce/PWL/const, int8 lanes) starts earning its keep.
