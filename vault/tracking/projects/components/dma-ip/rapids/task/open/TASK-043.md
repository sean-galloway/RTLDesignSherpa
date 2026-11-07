# TASK-043: move the inline TimeoutTB classes out of the scheduler timeout tests

**Priority:** P3
**Status:** open (filed 2026-11-07, the residual of TASK-042)
**Owner:** TBD

`dv/tests/fub/test_scheduler_timeout.py` and
`dv/tests/fub_beats/test_scheduler_timeout_beats.py` each define
`class TimeoutTB` at line 45, inside the test file. GLOBAL_REQUIREMENTS
("NEVER embed TB classes in test files") puts it in `dv/tbclasses/`. Neither
inherits `TBBase`.

Done when: one `TimeoutTB` (or the existing scheduler TB, if it covers the
case) lives in `dv/tbclasses/`, both tests import it, and both suites pass
through their Makefiles, clean-all first.
