# TASK-002: Bring the last three test areas onto the base coverage path -- CLOSED (2026-10-04)

> Migrated 2026-09-27 from `vault/Tasks/coverage/open.md` as **COV-001** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** closed 2026-10-04. The Makefile migration this task asked for had
already landed (apbx-xbar and retro_legacy in `71fe1ec5d` 2026-08-31 "converge
every dv/tests area onto make/tests.mk"; asic-trials in `76c6ff82b` 2026-09-15
"canonical dispatcher") — the item was stale at its own migration. Verification
against the tree found the migration was only skin-deep and finished the job:
see CLOSED below.
**Priority:** P3

Coverage collection and reporting are GENERIC now — any area whose
`dv/tests/Makefile` includes the base `make/tests.mk` gets
`COVERAGE=1 make run-all-*` and `make coverage-report` for free, and its
conftest delegates to `bin/cov_utils/conftest_base.py`. Verified 2026-08-09:
val/common, val/amba, val/integ_common, val/integ_amba, stream, rapids,
bridge and converters are all on it. Three areas are not:

- `projects/components/fabric-gen-ip/apbx-xbar/dv/tests/Makefile`
- `projects/components/retro_legacy_blocks/dv/tests/Makefile`
- `projects/asic-trials/timing_characterization/dv/tests/Makefile`

The fix per area is inclusion of the base tests.mk (see any val area's
Makefile for the pattern), NOT hand-rolled `run-coverage` targets — the
per-area replication is exactly what the base file replaced ([[coverage]]).
Watch for area-local Makefile conventions that conflict with the base
targets; that is the likely reason these three were deferred.

Blocked variants, noted not tasked: `delta` and `hive` have no dv tests at
all — coverage rollout there waits on tests existing.

---

## CLOSED 2026-10-04

**What was already done (at migration, unrecorded).** All three named areas
include `make/tests.mk` (four-line files for apbx-xbar and retro_legacy; a
target-forwarding dispatcher whose fub/ and top/ leaves are four-line files
for asic-trials) and all their conftests delegate to
`bin/cov_utils/conftest_base.py`.

**What verification found still missing.** `COVERAGE=1 make run-...` and
`make coverage-report` ran green in all three areas but produced zero
coverage data: the third leg — passing Verilator's `--coverage` flags into
the build — was never wired. Only val/common and pumice-fub do it (census
across every tests.mk area, measured this closure). Without it the report
prints "Tests: 0, .dat merged: 0, 0.0%" and looks like a pass.

**What this closure did.** Wired `get_coverage_compile_args()` into every
test runner of the three named areas following the val/common pattern
verbatim: apbx-xbar 6 files, retro_legacy_blocks 16 files (two `run()` calls
in test_apb4_rtc.py), asic-trials 10 files (9 fub + top, two calls in
test_char_top.py) — 32 files, ~64 lines, no other logic touched.

**Evidence (clean builds per the handbook, 2026-10-04).**
- apbx-xbar:  `COVERAGE=1 make run-apbx_xbar_1to1-gate-serial` green;
  `coverage-report` -> Line 90.6% (target 80%, PASS), .dat merged.
- retro_legacy: `run-apb4_gpio-gate-serial` green; report -> Line 90.2%
  PASS with per-file breakdown.
- asic-trials (fub): `run-inverter_chain-gate-serial` green; report ->
  Line 100.0% PASS.
("Tests: 0 / Protocol 0.0%" in these reports is the functional-coverage
column, which these areas do not collect; the line column is the one this
task is about.)

**Filed for the tooling lane:** coverage ISSUE-001 — the same compile-args
wiring is missing repo-wide (converters 0/23, rapids fub 0/10,
reed-solomon fub 0/16, scoria fub 0/18, stream, bch, andesite, misc);
recommended structural fix (central injection + a .dat-producing ratchet)
plus the hand-wired three as the reference pattern.
