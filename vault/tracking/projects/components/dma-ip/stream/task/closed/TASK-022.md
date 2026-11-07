# TASK-022: descriptor-driven 2D/strided addressing via dma_address_gen (STREAM Extended)

> Migrated 2026-11-07 from `projects/components/dma-ip/stream/TASKS.md` as **TASK-101** (that file's own numbering, not this lane's). Classified against the tree, not the file's stale "Idea / not started" marker.

**Priority:** P3 (opt-in extension; base STREAM unchanged)
**Status:** CLOSED 2026-07-29 -- built in three phases (pkg, descriptor_engine second-half fetch, scheduler run-base generators; 192254872 2026-07-06, f2a0fbe2b 2026-07-07) and regression-tested at the top (e28cf1ab4 2026-07-29). The chained-transpose corruption those tests found was stream BUG-010 (was TASK-059), fixed the same day.
**Owner:** sean galloway

## What it is

Strided, 2D-tiled, circular, reverse and transpose addressing for STREAM as an
opt-in extension. Compile-time gate `USE_ROW_COL_MAJOR_ADDRESSING`: at 0 the
scheduler and descriptor engine are the base tutorial engine; at 1 the
hardware accepts 256-bit legacy and 512-bit extended descriptors, chosen per
descriptor by `desc_type` ([210:208] of chunk 0), and two run-base generators
(read and write) drive the addresses.

## Where it lives

- `projects/components/utility-ip/misc/rtl/stream_run_addr_gen.sv` -- one
  `dma_address_gen` plus a run-base FIFO per direction (moved to utility-ip,
  shared with RAPIDS).
- `projects/components/dma-ip/stream/rtl/includes/stream_pkg.sv` -- `desc_type`,
  extended descriptor half.
- `projects/components/dma-ip/stream/rtl/fub/scheduler.sv` /
  `scheduler_core.sv` -- run-contiguous (`stride_0 == beat_size`, bursts) and
  per-beat 2-D (`stride_0 != beat_size`, single-beat AXI) modes.
- Summary: `vault/tracking/projects/components/dma-ip/stream/AT-A-GLANCE.md`
  "Addressing".

## Acceptance, as delivered

- [x] param=0 build unchanged; legacy FUB tests green at param=0, both modes elaborate.
- [x] Two addr-gens with run-ahead base FIFOs; scheduler consumes via valid/ready.
- [x] descriptor_engine fetches the second 256-bit half only for `desc_type=1`.
- [x] Mixed legacy + extended chain: `test_stream_top_extended`.
- [x] Transpose, including chained: `test_stream_top_extended_chained_transpose`.
- [x] stream-g equivalence bench carries extended run and per-beat scenarios
      (`dv/tests/fub_g/test_stream_g_equiv.py`).

Design choice recorded in the original: run-contiguous granularity (one base
per run of `inner_count` beats) chosen over per-beat for the burstable side;
`INDEX_WIDTH=16` limits a descriptor to 65,535 runs or beats.
