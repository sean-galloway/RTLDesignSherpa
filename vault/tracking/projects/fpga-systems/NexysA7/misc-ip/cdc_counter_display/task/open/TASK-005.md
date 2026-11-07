# TASK-005: metastability injector so RTL sim can show mode 0 failing

**Priority:** P3
**Status:** open (filed 2026-11-07; CDC_DEMO_TODO open question 3, "likely yes", plus `demo_5b_broken_but_static`)
**Owner:** TBD

RTL simulation does not model metastability, so the cocotb test passes in mode
0 at any clock while the board shows garbage above a few hundred kHz
(`docs/CDC_FAILURE_MODES.md` 4d). That contrast is the demo's lesson, but it
can only be shown on hardware today.

The plan's idea: a testbench helper that, on each destination edge, randomly
delays the source bits by a fraction of a destination clock (per bit,
independently), so a raw multi-bit crossing produces never-sent values in sim.
With it:
- mode 0 at a fast clock fails in sim the way it fails on the board;
- modes 2-4 still pass with the injector on (they must -- that is the proof);
- the plan's static case (5b: one write, read back correctly every time) can be
  shown passing with and without injection.

Gate-level SDF simulation (the plan's other route to 5b) is not in scope.
