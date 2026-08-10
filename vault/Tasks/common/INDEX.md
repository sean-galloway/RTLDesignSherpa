# common — task rollup

Canonical tracker for `rtl/common/` (~57 reusable building blocks).
Migrated 2026-07-23 from `rtl/common/TASKS.md`.

| Page | Count | What |
|---|---|---|
| [active.md](active.md) | 0 | in progress right now |
| [open.md](open.md) | 2 | accepted, not started |
| [closed.md](closed.md) | 18 | done (kept for history) |
| [dropped.md](dropped.md) | 2 | ended without completing |

The library is a stable, mature baseline: all modules production-ready, 100%
module test coverage, no blocking issues. Activity is maintenance, coverage and
integration support.

## Open shortlist

- **COMMON-003** — CLOSED 2026-08-09: rescoped twice (Sean) and delivered as
  `docs/markdown/rtl-integ-common/technique-index.md` — techniques mapped to
  their real, tested worked examples in projects/ instead of toy designs
  that would duplicate them. No new RTL by design; see closed.md.
- **COMMON-020** — CLOSED 2026-08-09: fifo_sync wavedrom now emits 4 diagrams
  per config and asserts non-empty. Three stacked defects (no constraints,
  wrong clock-group name, prefixed bindings) + the auto-draining FIFOSlave;
  see closed.md.
- **COMMON-021** — CLOSED 2026-08-09 (same day): formal refresh — audit found
  only 7/48 flat files repo-wide are current (common's is); all "prove-only"
  and icg cover gaps had already closed (verified fresh, all covers reached);
  bonus: all 147 math .sby were path-broken since the math split, repaired
  (full re-run = MATH-006). See closed.md + formal/FORMAL_TODO.md.
- **COMMON-010** — CLOSED 2026-08-09. The gap was "nothing enforces it"; CI now
  hard-gates `--check` and `--audit`, and common carries zero exemptions.
- **COMMON-016/017/018** — CLOSED 2026-08-05, fixed in the DV framework
  (`registered_grant`, the `r_last_valid` mirror in the compliance replay, and
  queued in-order ACKs). Both arbiter TBs now assert on the compliance verdict
  with no exclusions. See closed.md.
- **COMMON-019** — CLOSED 2026-08-07 (RTLDesignSherpa-DV#50). An ACK-mode grant
  handed between clients without `grant_valid` dropping never retired the old
  owner, so the model's mask lagged one grant forever. ACK mode now asserts on
  the compliance verdict.
- **COMMON-003** — integration examples (P2).
- **COMMON-007/008** — deferred enhancements (P3): arbiter types, multi-byte
  CRC. COMMON-006 (parameterized adders/multipliers) and COMMON-009
  (BCH/Reed-Solomon) DROPPED 2026-08-09 — generation stays the approach for
  the former; R/S, if it happens, is a future `projects/components/reed-solomon/`
  component, not library work (see dropped.md).

Practice and rationale live in the [handbook](../../handbook/INDEX.md);
this directory tracks *work* only. `/GLOBAL_REQUIREMENTS.md` wins on conflict.
