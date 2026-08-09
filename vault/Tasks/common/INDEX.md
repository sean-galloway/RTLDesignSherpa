# common — task rollup

Canonical tracker for `rtl/common/` (~57 reusable building blocks).
Migrated 2026-07-23 from `rtl/common/TASKS.md`.

| Page | Count | What |
|---|---|---|
| [active.md](active.md) | 1 | in progress right now |
| [open.md](open.md) | 5 | accepted, not started |
| [closed.md](closed.md) | 16 | done (kept for history) |
| [dropped.md](dropped.md) | 0 | ended without completing |

The library is a stable, mature baseline: all modules production-ready, 100%
module test coverage, no blocking issues. Activity is maintenance, coverage and
integration support.

## Open shortlist

- **COMMON-020** — CLOSED 2026-08-09: fifo_sync wavedrom now emits 4 diagrams
  per config and asserts non-empty. Three stacked defects (no constraints,
  wrong clock-group name, prefixed bindings) + the auto-draining FIFOSlave;
  see closed.md.
- **COMMON-021** — ACTIVE 2026-08-09: formal refresh for common — flat-file
  staleness audit, counter_freq_invariant re-prove, cover closure for the
  prove-only modules, icg cover fix. See formal/FORMAL_TODO.md.
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
- **COMMON-006/007/008/009** — deferred enhancements (P3). COMMON-009 (BCH) is
  the only place BCH is tracked; the docs-only `components/bch/` placeholder was
  deleted 2026-07-23.

Practice and rationale live in the [handbook](../../handbook/INDEX.md);
this directory tracks *work* only. `/GLOBAL_REQUIREMENTS.md` wins on conflict.
