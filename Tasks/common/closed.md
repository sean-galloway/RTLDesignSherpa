<!-- Managed by the `tasks` convention: see /Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# common — Closed (done)

---

## COMMON-001 — Improve test coverage to 95%
**Status:** closed — 100% module coverage, exceeded the 95% target. P2.

Every module in `rtl/common/` has a test. Baseline coverage was ~90% with gaps
in clock utilities, synchronizers and miscellaneous modules.

## COMMON-002 — Waveform save files for all modules
**Status:** closed. P3.

GTKWave save files so a failing test opens with the relevant signals already
grouped rather than requiring them to be found by hand.

## COMMON-004 — Documentation consistency review
**Status:** closed — Phase 3 complete (all Priority 1 and 2 modules). P2.

Module documentation reconciled against the RTL: headers, parameter tables with
ranges, port lists, notes.

## COMMON-005 — Parameterization audit
**Status:** closed — audit complete. P3.

Modules scored on parameterization quality; Priority-1 modules (score < 60)
identified and addressed. See [[sizing-invariants]] for the practice this fed.
