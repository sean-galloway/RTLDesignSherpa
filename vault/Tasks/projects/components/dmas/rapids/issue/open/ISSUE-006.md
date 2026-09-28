# ISSUE-006: under memory latency the sink keeps only ~12 beats in flight per channel, far below what PIPELINE=1 allows

**Priority:** Low -- a characterization finding, not a defect; the sink runs at
line rate at the latencies the harness's memory model gives it (99.9 % to 48
cycles of injected response delay).
**Status:** OPEN 2026-09-28. From the v1.4 perf report, section 7.5.

## What was measured

Genesys 2, 8 channels x 1024 beats, PIPELINE = 1, `AW_MAX_OUTSTANDING = 8`,
8-beat bursts, `RESP_DELAY` sweep on the observers bitstream. By Little's law
the sink write path asymptotes to `0.182 x 512 = 93` beats in flight across 8
channels (~12 per channel), while eight 8-beat AWs per channel could hold 64.
The source read path on the same sweep holds `0.937 x 512 = 480` (~60 per
channel), so the read engine does use its outstanding depth; the write engine
is bounded by something else.

## Candidates

The sink SRAM's per-channel allocation (`cfg_alloc_size`, `SRAM_DEPTH / NC` =
64 beats per channel) and the commit accounting that frees space only when a
burst's B returns; the W-phase FIFO (`W_PHASE_FIFO_DEPTH = 64` beats, shared);
the write engine's data-availability gate, which will not issue an AW until the
whole burst is in SRAM. Find which one binds (a sim sweep of `RESP_DELAY` with
the harness reproduces the board numbers), then decide whether a deeper window
is worth its BRAM.
