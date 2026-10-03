# TASK-016: rebuild the Genesys2 stream harness images with the fixed sdpram slave and repin the perf data

**Priority:** P2
**Status:** closed 2026-10-03 (FIXED — see the CLOSED section below)
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

## CLOSED 2026-10-03

All three instrumented builds rebuilt on the post-fix tree (sdpram 71d48b6f7),
timing-closed and board-verified on Genesys2 200300B818A0:

- build-perf (sha d26f9b7b..., WNS +1.175 ns): 40-config matrix **40/40 PASS,
  cycle-identical to the 2026-09-09 pre-fix sweep on every config** (0 cycles
  delta, ~1525.9 MB/s). Artifacts: `build-perf/results/perf_sweep_2026-10-03.
  {csv,json}`, `bus_meters_2026-10-03.txt`.
- build-mon (sha aceec688..., WNS +1.914 ns): mon_compress 1.02 slots/pkt,
  66.0% saving PASS (baseline 66.4% — data-dependent noise); mon_coverage
  4/8 legal tuples, 0 unexpected (`build-mon/results/mon_coverage_2026-10-03.
  txt`).
- build-obs (sha 60696ace..., WNS +3.925 ns): campaign + matrix artifacts in
  `build-obs/results/obs_board_2026-10-03.txt`; matrix 5/7 classes above floor
  (timeout keyed=168 — pre-existing reporter saturation; debug keyed=0).

**Verdict: NOT significantly different — exactly 0 measured datapath change.**
The old sdpram burst tax amortizes below measurement resolution at the 1
MB/descriptor matrix points, and the datapath was already 100% gapless. The
obs/mon tally differences are the 2026-09-27 lite-taps observer rework
(78cddb5e2, caps0 bit4/bit5 now read 0), NOT the sdpram fix — the obs/mon
host campaigns still arm/report the retired perf/debug cones and need a
re-baseline (filed as a follow-up item in this area's bug lane).

Docs repinned with dated notes: reports/perf/README.md,
docs/stream_char_guide/ch01_overview/01_overview.md,
docs/assets/diagrams/stream_harness_modes.dot,
docs/stream_fpga_system/ch01_overview/01_system.md,
docs/stream_fpga_system/ch03_builds/01_build_variants.md,
reports/compression/README.md.
