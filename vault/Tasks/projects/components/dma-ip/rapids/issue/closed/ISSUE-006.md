# ISSUE-006: under memory latency the sink keeps only ~12 beats in flight per channel, far below what PIPELINE=1 allows

**Priority:** Low -- a characterization finding, not a defect; the sink runs at
line rate at the latencies the harness's memory model gives it (99.9 % to 48
cycles of injected response delay).
**Status:** CLOSED 2026-09-28 (closing note at the end); was OPEN 2026-09-28,
from the v1.4 perf report, section 7.5.

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

---

**CLOSED 2026-09-28.** Reproduced in the harness simulation (8 channels x
1024 beats, `SRAM_DEPTH = 256` as on the Genesys 2, 256 cycles of write-response
delay through the new `TEST_RESP_DELAY_WR` / `TEST_SRAM_DEPTH` knobs): the sink
write meter reads 34.7 %, the board's own number for that row. The dump shows
the mechanism, and it is the stimulus, not the DUT:

- the write engine's outstanding count sums to 7.9 across the eight channels
  in steady state, and on average exactly one channel has `w_data_ok`: the whole
  `AW_MAX_OUTSTANDING = 8` window belongs to ONE channel at a time;
- the harness's AXIS generator (`axis4_master_injector`) streams channels
  sequentially by design -- "finish one channel, then the next", so each
  channel's LFSR sequence is contiguous for the golden CRC -- so only one sink
  channel ever holds data, and the sink SRAM (256 beats per channel) is
  irrelevant to the window;
- the source path does not see this because the read engine pulls all eight
  channels from memory concurrently.

So the sink's in-flight window under memory latency is one channel's
`AW_MAX_OUTSTANDING x burst = 8 x 8 = 64` beats, plus the bursts in their W
phase: `0.182 x 512 = 93` on the board is that window, not a DUT bound. None of
the candidates in the issue (SRAM allocation, the W-phase FIFO, the
data-availability gate) is involved. Measuring the DUT's aggregate window needs
a generator that interleaves channels beat by beat; that is a harness feature
(rapids TASK-018), and the report's 7.5 text now says what the column measures.
