# TASK-016: rebuild the Genesys2 stream harness images with the fixed sdpram slave and repin the perf data

**Priority:** P2
**Status:** open
**Owner:** TBD

amba 71d48b6f7 (2026-10-02) fixed `rtl/amba/shared/sdpram_core.sv`: burst
commands now queue two deep per direction and the tracker reloads the cycle
the active burst completes, so a burst boundary is FREE. The old core charged
~2.0 cycles per write burst and ~1.6 per read burst at every boundary, and
every board-measured figure this area pins was taken with that cost in the
path. The RS AXI4 harness (the proof case) moved 249.65 -> 244.00 cyc/block
with its codeword seams going 97.0%/98.5% -> 100.0%/100.0%, sim and board
agreeing to the digit.

## What to do

Rebuild and re-measure the Genesys2 stream harness (all three instrumented
builds share the sdpram through `stream_harness.f` /
`instrumentation_common.f`), then repin the docs:

- `projects/fpga-systems/Genesys2/stream/build-perf/`
- `projects/fpga-systems/Genesys2/stream/build-obs/`
- `projects/fpga-systems/Genesys2/stream/build-mon/`

Then repin every pinned figure taken with the pre-fix slave: the board
perf/monitor results (the 40/40 runs) and any doc/table quoting stream
board throughput.

## Done when

- Fresh images for all three builds close timing and pass their board
  smoke.
- Every doc/table that pins a board-measured figure either carries a
  post-fix number or a dated note saying the figure is pre-fix.

## Not in scope

- The sdpram fix itself (done, amba 71d48b6f7; full val/amba regression
  2234/2234).
- pumice and rapids harnesses — filed separately (pumice TASK-038, rapids
  TASK-023).
- Any attempt to improve the numbers beyond what the fix delivers; this is
  a re-pin, not a new perf push.
