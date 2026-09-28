# coverage — task rollup

**Next ID: COV-003** — never recycle a number, even when its task closed.

## Lanes

This area tracks three kinds of work, each a directory with its own INDEX and
its own ID sequence. **Every item is its own file**, `<ID>.md`, filed under
the directory for its state (`open/`, `active/`, `closed/`, `dropped/`).
Pick the lane before filing:

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 2 | 0 | 1 | 1 | 0 |
| [bug/](bug/INDEX.md) | 1 | 0 | 0 | 0 | 0 |
| [issue/](issue/INDEX.md) | 1 | 0 | 0 | 0 | 0 |

Items live one per file under the lane directories below; this page is the
area overview. See [the convention](../INDEX.md) for the definitions.


Verilator/functional coverage rollout across test areas. Migrated 2026-08-09
from `val/COVERAGE_TODO.md` (dated 2026-03-20), classified against reality:
most of that tracker had already landed via the shared `make/tests.mk` +
`bin/cov_utils/` consolidation the handbook describes.

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 1 | 0 | 1 | 1 | 0 |
| [bug/](bug/INDEX.md) | 0 | 0 | 0 | 0 | 0 |
| [issue/](issue/INDEX.md) | 0 | 0 | 0 | 0 | 0 |

Method lives in the handbook ([[coverage]] note: how to run, toggle-vs-line
semantics, the monbus matrix); thresholds live in
`bin/cov_utils/unified_coverage_report.py` and
`docs/user-guides/rtl_coverage_guidelines.md`. This area tracks WORK only.

## Open shortlist

- **COV-001** — the three test areas still off the base `tests.mk` coverage
  path: apbx_xbar, retro_legacy_blocks, timing_characterization.

