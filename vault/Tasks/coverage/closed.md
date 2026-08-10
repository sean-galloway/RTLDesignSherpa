<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# coverage — Closed (done)

---

## COV-000 — Coverage infrastructure consolidation (historical record)
**Status:** CLOSED — work landed across 2026-03..2026-07; recorded at
migration 2026-08-09 from val/COVERAGE_TODO.md

The rollout the old tracker was tracking is done, and went further than its
plan: instead of pasting Makefile targets + conftest blocks per component
(the tracker's "What Needs to Be Done Per Component" template), the
machinery consolidated into ONE implementation — base `make/tests.mk`
(collect + report targets), `bin/cov_utils/conftest_base.py` +
`conftest_coverage.py` (shared conftest hooks), MAX-based hit merging,
separate line/branch/toggle reporting, coverage waivers YAML,
`unified_coverage_report.py` (`make coverage-unified`), a CI gate
(`.github/workflows/coverage.yml`), and auto-detected scenario status from
JUnit XML. stream/rapids/bridge/converters plus the val family all ride it.
The handbook [[coverage]] note is the method reference.
