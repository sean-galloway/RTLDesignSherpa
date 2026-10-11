# ISSUE-001: Shell TEST_LEVEL env overrides per-cell extra_env in cocotb_test runs

**Priority:** P3
**Status:** OPEN
**Owner:** TBD
**Filed:** 2026-10-11

## Observation

When running the converter cocotb-test test runners, a `TEST_LEVEL` value set in the calling shell overrides the per-cell `extra_env['TEST_LEVEL']` value passed to `cocotb_test.simulator.run()`. This has been confirmed empirically on the canonical command:

```
TEST_LEVEL=func PYTHONPATH=/mnt/data/github/RTLDesignSherpa-DV-dev/src venv/bin/python -m pytest ...
```

The pytest parametrization still advertises the intended per-cell level (e.g., `gate`, `func`, `full`), but the actual simulation sees the shell value and silently downgrades `full` cells to `func`.

## Why it matters

The repo-wide convention of exporting `TEST_LEVEL` to choose a regression class collides with cocotb-test's environment-forwarding behavior. Full-coverage cells can run with a reduced test vector set without any visible failure, weakening regression proofing.

## Candidate disposition

- Explicitly clear `TEST_LEVEL` from `os.environ` inside the test-runner functions before calling `run()`, so the `extra_env` dict is the sole source of truth.
- Or: change the canonical command and CI to stop exporting `TEST_LEVEL` globally, relying instead on per-cell `extra_env` and `REG_LEVEL` filtering.
- Add a guard assertion that fails fast if the shell `TEST_LEVEL` differs from the cell's requested level.

This is a pre-existing repo-wide convention; this issue tracks the converters area and any regression-proofing needed before the AXI3 converter work is considered fully closed.
