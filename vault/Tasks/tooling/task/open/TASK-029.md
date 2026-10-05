# TASK-029: validate cocotb-coverage on cocotb 2.1.0 — the last blocker on the production pin flip

**Priority:** P2
**Status:** open
**Owner:** TBD
**Filed:** 2026-10-04
**Refs:** [[TASK-025]] (the 2.x migration this gates), tooling ISSUE-003, RDS-DV `pyproject.toml:46-50`

## Why this exists

The 2.1.0 migration is functionally DONE — bridge/math/common/cdc are green on
cocotb 2.1.0 (`venv-cocotb2/`), with every fix dual-version and the 1.9.2
controls unchanged. But the production pin has NOT flipped:

    requirements.txt:   cocotb==1.9.2
                        cocotb-coverage==1.2.0     <-- incompatible with cocotb 2.x

`cocotb-coverage` 1.2.0 is the one remaining package that cannot coexist with
cocotb 2.x (pip itself reports the conflict on install). Every coverage run in
the repo (`COVERAGE=1 make run-all-*`, wired into every area's conftest) breaks
the day `cocotb==2.1.0` lands in the shared venv. Until this task closes, the
2.1.0 flip is a one-line change that is nevertheless forbidden.

## What to do

1. **Install the candidate** in the existing 2.x venv:
   `source env_python && source venv-cocotb2/bin/activate && pip install cocotb-coverage`
   (latest 2.x; note pip will want to remove cocotb 1.x-era pins — let it resolve
   against cocotb 2.1.0 and report what version landed).
2. **Read its changelog first.** cocotb-coverage 2.0 rewrote around cocotb 2.x
   APIs; if it dropped/changed decorators or the `coverage` module surface that
   the areas' conftests use (`os.environ['COVERAGE']` gating per
   `make/tests.mk`), that is a code change here, not just a pin bump.
3. **Run one BKM area with coverage on**: from a test area,
   `COVERAGE=1 make run-all-func-parallel` (or gate, if slow) under
   `venv-cocotb2`. Compare the coverage artifact set against a 1.9.2 control
   run of the same area — same database type, same report generation, no
   crash in conftest collection.
4. **Unpin on success, in both repos:** RDS `requirements.txt`
   (`cocotb-coverage==1.2.0` → the validated version) and the
   `"cocotb-coverage<2"` cap in RDS-DV `pyproject.toml` (added 2026-09-30,
   commit `ed6defb`, with the 0.2.1-cap precedent for revisiting stated
   reasons).
5. **Then flip the pin** as its own commit: `cocotb==2.1.0` (+ `cocotb-bus==0.3.0`
   already validated in TASK-025) in `requirements.txt`, shared-venv rebuild,
   and the BKM matrix re-run as the gate.

## Hazards

- **Do not skip step 2.** The 0.6.9 release shipped documentation teaching the
  very idiom the release removed, because a grep covered the wrong file set
  ([[TASK-025]]'s own history). Verify the installed artifact, not the repo.
- The shared venv MUST stay 1.9.2 until step 5 — it is the control every
  2.x result is compared against.
- If cocotb-coverage 2.0 cannot validate (upstream regression, dropped
  feature the areas rely on), the fallback is recording that and keeping
  coverage pinned to the 1.9.2 venv permanently — a split-venv policy that
  needs an owner decision, not a silent default.

## Done when

- One BKM area produces a valid coverage database under cocotb 2.1.0 with
  cocotb-coverage 2.x, matched against a 1.9.2 control.
- Both pins updated (or the split-venv fallback recorded as a decision).
- The `cocotb==2.1.0` flip committed with a green BKM re-run.
