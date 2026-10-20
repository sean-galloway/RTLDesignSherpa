# TASK-007: Close the M1-M8 numeric-policy open items at FPGA bring-up

**Priority:** P3
**Status:** open -- 2026-10-19
**Owner:** sean galloway

## Why

The alu-infer MAS carries eight open numeric-policy items. They are
correctly triaged as bring-up questions (owner: latency calls happen once
the ALU is on the FPGA), but they need one sweep so they don't fossilize.

## What

At M1 bring-up (tetrad on the FPGA, tile milestone ladder), close out:

- M1 — NaN/inf semantics in min/max and activations.
- M2 — whether library IEEE exception outputs forward into `result_flags`.
- M3 — denormal/FTZ policy, cell-wide vs per-block (library defaults FTZ).
- M4 — `threshold_imm` encoding (raw bf16 pattern vs converted small int).
- M6 — `func_sel[8:7]` element-width disposition — SUPERCEDED by the
  2026-10-19 format roadmap (TASK-004 int8, TASK-005 fp32); close it here
  when those land.
- M8 — `ROW_LATENCY` value and per-row natural-latency table from measured
  FPGA timing (RTL default 4, range [1,6]).
- (M5/M7 already resolved: M7 mac presents post-update accumulator rounded
  to bf16 — verify the list against the MAS when sweeping.)

## Done when

Every M-item in the alu-infer MAS is marked resolved with the measured
answer, or moved to a task of its own.
