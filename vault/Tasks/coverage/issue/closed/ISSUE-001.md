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

## CLOSED 2026-10-04 — resolved into the structural fix, implemented and validated

**Design decision (the tooling-lane question this issue posed):** inject
centrally, do not wire ~200 test files. The seam is
`cocotb_test.simulator.run`: pytest imports every area's conftest (which
delegates to `bin/cov_utils/conftest_base.py`) and runs its `configure()`
BEFORE collecting test modules, and test modules bind
`from cocotb_test.simulator import run` at import time -- so wrapping the
module attribute once in `configure()` reaches every area with zero
per-file changes.

**What landed (2026-10-04):**
- `bin/cov_utils/conftest_base.py`: `_ensure_coverage_compile_args_hook()`
  wraps `cocotb_test.simulator.run` once per process; the wrapper appends
  `get_coverage_compile_args()` at CALL time only when `COVERAGE=1`, dedupes
  against flags a test file added itself, and never removes arguments.
- `bin/cov_utils/merge_testlevel_coverage.py`: the ratchet -- a report with
  0 merged .dat now prints a clear stderr message and exits 1 (a 0.0% report
  is a defect, not a pass).
- `vault/handbook/dv/coverage.md`: the injection + ratchet documented in the
  coverage how-to.

**Validation (2026-10-04, clean builds):**
- converters (previously 0/23 wired): `COVERAGE=1 make
  run-axi_data_upsize-gate-serial` -> 2 .dat, report Line 96.3% PASS. The
  central hook alone produces data where per-file wiring never existed.
- Plain run (no COVERAGE=1): passes, no `coverage_data/` created, zero
  `--coverage` in the build log -- the wrapper is inert off-toggle.
- val/common (already per-file wired): still passes under COVERAGE=1 -- the
  wrapper dedupes instead of double-adding flags.
- Ratchet live: `make coverage-report` in an area with no coverage data
  exits nonzero with the explanatory message.

**Optional follow-up (not filed as a task; ride a future cleanup):** strip
the now-redundant per-file `get_coverage_compile_args()` wiring in
val/common, pumice-fub, and the three coverage-TASK-002 areas. The wrapper
dedupes, so the duplication is harmless -- it is purely less code to read.
