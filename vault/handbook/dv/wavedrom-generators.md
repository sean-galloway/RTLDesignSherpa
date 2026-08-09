---
title: Wavedrom generators
summary: The constraint-solver traps that make a wavedrom test emit nothing and pass; the working reference; the non-empty assert.
---

# Wavedrom generators

Wavedrom tests exist to emit the wave JSON the docs point at. Their entire
deliverable is that JSON, so **a run that emits none is a failure, never a
pass** — every wavedrom test must end with
`assert len(results['solutions']) > 0`, and must assert that
`setup_wavedrom()` actually produced a solver (its except clause typically
nulls `wave_solver`, and if every wavedrom step is guarded on it, a broken
setup sails through green). Both doors were open in
`val/common/test_fifo_sync_wavedrom.py`, which printed "GENERATION COMPLETE"
over zero output for months (COMMON-020, closed 2026-08-09).

**The working reference is `val/amba/test_gaxi_fifo_sync.py`'s wavedrom test.**
Port from it; do not write solver plumbing from scratch.

## The traps (each alone produces zero JSON, silently)

1. **No constraints registered.** `WaveJSONGenerator` groups and signal
   bindings are NOT enough — nothing reaches `save_wavejson()` except a solved
   `TemporalConstraint`. No `add_constraint()` call means the sampling loop
   iterates an empty set and captures nothing.
2. **The clock group must be named `'default'`.** Every `TemporalConstraint`
   defaults to `clock_group='default'`, and the sampler *silently skips*
   constraints whose group name does not match a registered clock group. Name
   the group anything else and every window stays at 0 cycles forever.
3. **`add_interface(name, ...)` prefixes every binding with `name_`.** The
   constraint events and `signals_to_show` then reference names that were
   never bound. Use direct unprefixed `add_signal_binding()` calls (the
   reference's pattern), matching the names the generator groups use.
4. **A base TB's reactive consumer fights scripted stimulus.** `FifoBufferTB`
   starts an auto-consuming `FIFOSlave`; with it alive the FIFO never fills,
   so full/almost-full constraints can never match — and the diagrams are not
   reproducible anyway. Kill the consumer (`tb.read_slave.kill()`) and own
   the pin; wavedrom stimulus must be deterministic ([[seeds-and-determinism]]:
   fixed seed, exact drive).

## Solver mechanics worth knowing

- Windows are per-constraint rolling deques of `max_window_size`; the sampler
  auto-solves each constraint whenever its window fills and stops at
  `max_matches`. One long sampling session therefore captures multiple
  scenarios, PROVIDED each constraint keys on a distinct single-signal
  transition that the stimulus produces deterministically (first `write`,
  `wr_full` 0->1, `rd_empty` 0->1, ...). `SignalTransition` is single-signal:
  a "simultaneous read+write" scenario cannot be targeted by event alone —
  the reference isolates such scenarios by sampling only around them
  (start/stop/solve/clear per scenario).
- `solve_and_generate()` at the end only mops up constraints whose window
  never filled; it is not the primary solve path.

Related: [[silent-fallbacks]] — this is that pattern with a JSON deliverable;
[[test-runner]] for the REG_LEVEL grid wavedrom tests still must carry.
