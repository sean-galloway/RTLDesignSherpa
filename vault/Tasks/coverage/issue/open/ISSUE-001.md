# ISSUE-001: coverage data collection is unwired repo-wide — `coverage-report` runs but reports 0% almost everywhere

**Status:** open 2026-10-04. Surfaced closing coverage TASK-002.
**Priority:** P3 — the plumbing works and reports honestly; the missing piece is
per-test-file Verilator flag wiring.

## What works

`make/tests.mk` gives every migrated area the run targets, the `COVERAGE=1`
passthrough, and `make coverage-report`; every area's conftest delegates to
`bin/cov_utils/conftest_base.py`, which creates `coverage_data/` and
aggregates whatever `.dat` files exist.

## What does not

The third leg — passing Verilator's `--coverage` flags into the build — is
wired only where a test file explicitly calls
`get_coverage_compile_args()` (from `bin/cov_utils/conftest_coverage.py`)
and extends its runner's compile args. Measured 2026-10-04 across every
tests.mk area: only `val/common` (direct files) and pumice's fub (via the
`pumice_coverage` helper) do it. Everything else — converters 0/23, rapids
fub 0/10, retro_legacy 0/16, reed-solomon fub 0/16, scoria fub 0/18,
stream, bch, andesite, misc — runs green under `COVERAGE=1` and produces
zero `.dat`; `coverage-report` then reports "Tests: 0 ... 0.0%" with no
warning that anything is wrong.

## Why it is an ISSUE not a TASK yet

The fix shape is mechanical per file (two lines) but the file count is
~200, and the honest long-term answer is probably structural: inject the
coverage args centrally (e.g. from `conftest_base.configure` via a cocotb
build-env hook, or a tests.mk-passed `VERILATOR_FLAGS` convention) so test
files never wire it by hand. That is a design decision for the tooling
lane, plus a ratchet check that would have caught this (e.g. gate:
`COVERAGE=1` run must produce ≥1 `.dat`, or the report must refuse to
print 0-merged as success). TASK-002's three named areas were wired by
hand 2026-10-04 as the reference pattern.
