# TASK-023: rebuild the Genesys2 rapids harness images with the fixed sdpram slave and repin the perf data

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

NOTE: the `rapids_byte_perf_prelim_*.json` reports captured 2026-10-02 were
measured on images built BEFORE the fix -- treat them as pre-fix baselines,
not as current numbers.

## What to do

Rebuild and re-measure both Genesys2 rapids harnesses that pull the sdpram,
then repin the docs:

- `projects/fpga-systems/Genesys2/rapids/` (`rapids_byte_harness.f`) —
  the byte perf + monitor images.
- `projects/fpga-systems/Genesys2/rapids_beats/flows-rapids-beats/`
  (`rapids_char_harness.f`) — the char harness.

Then repin every pinned figure taken with the pre-fix slave:
`reports/perf/` JSONs, and any doc/table quoting rapids board throughput.

## Done when

- Fresh images for both harnesses close timing and pass their board smoke.
- Every doc/table that pins a board-measured figure either carries a
  post-fix number or a dated note saying the figure is pre-fix.

## Not in scope

- The sdpram fix itself (done, amba 71d48b6f7; full val/amba regression
  2234/2234).
- pumice and stream harnesses — filed separately (pumice TASK-038, stream
  TASK-016).
- TASK-022 (byte-specific proofs) and any other active rapids work; this is
  a re-pin, not new feature work.
