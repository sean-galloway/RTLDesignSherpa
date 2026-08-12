<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# coverage — Open (accepted, not started)

---

## COV-001 — Bring the last three test areas onto the base coverage path
**Status:** open 2026-08-09 (the surviving remainder of val/COVERAGE_TODO.md,
verified against the tree at migration)
**Priority:** P3

Coverage collection and reporting are GENERIC now — any area whose
`dv/tests/Makefile` includes the base `make/tests.mk` gets
`COVERAGE=1 make run-all-*` and `make coverage-report` for free, and its
conftest delegates to `bin/cov_utils/conftest_base.py`. Verified 2026-08-09:
val/common, val/amba, val/integ_common, val/integ_amba, stream, rapids,
bridge and converters are all on it. Three areas are not:

- `projects/components/apbx_xbar/dv/tests/Makefile`
- `projects/components/retro_legacy_blocks/dv/tests/Makefile`
- `projects/NexysA7/timing_characterization/dv/tests/Makefile`

The fix per area is inclusion of the base tests.mk (see any val area's
Makefile for the pattern), NOT hand-rolled `run-coverage` targets — the
per-area replication is exactly what the base file replaced ([[coverage]]).
Watch for area-local Makefile conventions that conflict with the base
targets; that is the likely reason these three were deferred.

Blocked variants, noted not tasked: `delta` and `hive` have no dv tests at
all — coverage rollout there waits on tests existing.
