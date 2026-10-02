# TASK-038: rebuild the ddr2-char harness images with the fixed sdpram slave and repin the perf data

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

Rebuild and re-measure every pumice-family board harness that pulls the
sdpram, then repin the docs:

- `projects/fpga-systems/NexysA7/pumice/build-perf/`
  (`ddr2_char_harness.f`) — the pumice board perf characterization image.
- `projects/fpga-systems/NexysA7/pumice/ddr2-characterization/flows-litedram-uart/`
  (`litedram_char_harness.f`) — the LiteDRAM same-harness A/B image; BOTH
  sides of the A/B move, so the comparison needs re-running, not editing.
- Sim-side equivalence checks that assert cycle windows
  (`ddr2_char_framework` cosim) — re-baseline expectations the way
  `test_rs_loop_uart.py` was (58d123430) if any window moved.

Then repin every pinned figure taken with the pre-fix slave: the board perf
char numbers, the LiteDRAM A/B table, the bank/gap knee data
(PUMICE-036) if it moved, and any HAS/MAS chapter quoting board-measured
throughput. `pumice_char.py --char/--char-scale` is the measurement entry
point.

## Done when

- Fresh images for both harnesses close timing and pass their board smoke.
- Every doc/table that pins a board-measured figure either carries a
  post-fix number or a dated note saying the figure is pre-fix.
- The pumice-vs-LiteDRAM A/B is re-measured on images built from the same
  commit, same as the original methodology.

## Not in scope

- The sdpram fix itself (done, amba 71d48b6f7; full val/amba regression
  2234/2234).
- rapids and stream harnesses — filed separately (rapids TASK-023, stream
  TASK-016).
- Any attempt to improve the numbers beyond what the fix delivers; this is
  a re-pin, not a new perf push.
