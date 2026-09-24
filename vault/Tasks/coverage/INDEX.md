# coverage — task rollup

**Next ID: COV-003** — never recycle a number, even when its task closed.

## Lanes

This area tracks three kinds of work, each with its own lifecycle pages and its
own ID sequence. Pick the lane before filing:

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `TASK-001` |
| [bug/](bug/INDEX.md) | a defect with a reproduction | `BUG-001` |
| [issue/](issue/INDEX.md) | an anomaly/risk/question not yet diagnosed | `ISSUE-001` |

**The pages at this level are the LEGACY task lane.** They are frozen: close
them out where they stand, and do not add to them. New work of any kind goes in
a lane above. See [the convention](../INDEX.md) for the full definitions.


Verilator/functional coverage rollout across test areas. Migrated 2026-08-09
from `val/COVERAGE_TODO.md` (dated 2026-03-20), classified against reality:
most of that tracker had already landed via the shared `make/tests.mk` +
`bin/cov_utils/` consolidation the handbook describes.

| Page | Count | What |
|---|---|---|
| [active.md](active.md) | 0 | in progress right now |
| [open.md](open.md) | 1 | accepted, not started |
| [closed.md](closed.md) | 1 | done (kept for history) |
| [dropped.md](dropped.md) | 1 | ended without completing |

Method lives in the handbook ([[coverage]] note: how to run, toggle-vs-line
semantics, the monbus matrix); thresholds live in
`bin/cov_utils/unified_coverage_report.py` and
`docs/user-guides/rtl_coverage_guidelines.md`. This area tracks WORK only.

## Open shortlist

- **COV-001** — the three test areas still off the base `tests.mk` coverage
  path: apbx_xbar, retro_legacy_blocks, timing_characterization.

