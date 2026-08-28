# coverage — task rollup

**Next ID: COV-002** — never recycle a number, even when its task closed.

Verilator/functional coverage rollout across test areas. Migrated 2026-08-09
from `val/COVERAGE_TODO.md` (dated 2026-03-20), classified against reality:
most of that tracker had already landed via the shared `make/tests.mk` +
`bin/cov_utils/` consolidation the handbook describes.

| Page | Count | What |
|---|---|---|
| [active.md](active.md) | 0 | in progress right now |
| [open.md](open.md) | 1 | accepted, not started |
| [closed.md](closed.md) | 1 | done (kept for history) |
| [dropped.md](dropped.md) | 0 | ended without completing |

Method lives in the handbook ([[coverage]] note: how to run, toggle-vs-line
semantics, the monbus matrix); thresholds live in
`bin/cov_utils/unified_coverage_report.py` and
`docs/user-guides/rtl_coverage_guidelines.md`. This area tracks WORK only.

## Open shortlist

- **COV-001** — the three test areas still off the base `tests.mk` coverage
  path: apbx_xbar, retro_legacy_blocks, timing_characterization.
