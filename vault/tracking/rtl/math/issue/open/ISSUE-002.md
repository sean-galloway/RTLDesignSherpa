# ISSUE-002: full ieee754 generator regen produces ~115 files of drift

**Priority:** P3
**Status:** OPEN (repo hygiene; no functional defect in shipped RTL)
**Owner:** TBD

## Observation

Running the documented full regeneration
(`PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/math`)
rewrites ~115 already-committed modules without functional intent:

1. Every file's `// Created: <date>` header stamp moves to the regen day.
2. A substantive template/RTL divergence: sequential modules regenerate with
   plain `always_ff @(posedge i_clk or negedge i_rst_n)` while the committed
   RTL uses the `reset_defs.svh` macros (`ALWAYS_FF_RST`, `RST_ASSERTED`).
   The committed files were not produced by the current generator state
   (template changed, or a partial regen was committed).

## Risk

The next person who runs the documented regen flow (as BUG-008 required)
either sweeps ~115 unrelated files into their commit or must hand-revert,
exactly the trap BUG-008's fix hit. Functional risk is nil today — the
divergence is style-level — but it will grow until reconciled.

## Candidate dispositions

- One-time reconcile: run the full regen, review the reset-macro delta
  across the sequential modules, commit as its own "generator reconcile"
  changeset so future regens are no-op diffs.
- Or: pin the generator to emit the reset macros and the original creation
  dates (don't stamp on regen), then reconcile.

## Log

**2026-10-10 -- filed** from the BUG-008 regeneration exercise.
