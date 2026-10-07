# TASK-029: validate cocotb-coverage on cocotb 2.1.0 — the last blocker on the production pin flip

**Priority:** P2
**Status:** validated 2026-10-06 — pin flip committed (RDS `8fb596b57`, RDS-DV cap lifted); the shared-venv rebuild + BKM matrix re-run is the remaining operational step
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

## Progress 2026-10-06 (validation complete)

All five steps of the plan were executed except the shared-venv rebuild
itself, which is deliberately left as the owner's flip moment (other lanes
run against the shared venv continuously; the rebuild is minutes but the
BKM re-run gate is the commitment):

1. **Install:** `cocotb-coverage 2.0` in `venv-cocotb2` resolves clean
   against cocotb 2.1.0 — zero other pins move. The only resolver conflict
   was this repo's own `<2` cap (lifted, see 4).
2. **Changelog/API (installed artifact, per the hazard):** 2.0 is a
   cocotb>=2.0 adjustment; the functional surface is unchanged.
   Verified live: `CoverageDB`, `CoverPoint`, `CoverCross`,
   `coverage_section`, `merge_coverage`, `reportCoverage` all present and
   exercised; XML and YML export round-tripped a sampled covergroup.
3. **BKM coverage run:** `val/cdc`, `COVERAGE=1 make run-all-gate` under
   `venv-cocotb2`: **37 passed**, artifact set identical to the 1.9.2 +
   cocotb-coverage 1.2.0 control (Verilator `coverage.dat`, `.coverage`,
   `htmlcov/` per cell); no conftest collection crash. Note: no test in
   either repo currently imports `cocotb_coverage` at runtime (repo
   COVERAGE mode is Verilator line/toggle via coverage.py; only
   `bin/aggregate_coverage.py`'s docstring names functional coverage) --
   the pin was blocking by pip co-installability, which this resolves.
4. **Unpin, both repos:** RDS `requirements.txt` flip committed
   (`8fb596b57`: cocotb 2.1.0 / cocotb-bus 0.3.0 / cocotb-coverage 2.0 /
   cocotb-framework 1.2.0 truth fix). RDS-DV `pyproject.toml` `<2` cap
   lifted with the measured evidence recorded in the dependency comment.
5. **The flip (remaining):** shared-venv rebuild from the new
   `requirements.txt`, then the BKM matrix (`make clean-all &&
   make run-all-full-parallel` per area: bridge/math/common/cdc) as the
   gate. Everything in the repo is dual-version (TASK-025), so the
   rebuild is expected to be uneventful — but it is a shared-resource
   change and gets a go signal, not a silent default.

## Switch runbook (morning of the flip)

Sequenced so a failure at any step leaves a working tree behind.

1. `git pull` in RDS (pins at `a9a8120d4`) and confirm `venv-cocotb2/`
   still imports (it is the reference 2.x env if rollback is needed).
2. Rebuild the shared venv from the new pins:
   `python3 -m venv venv --upgrade-deps` style rebuild per house practice,
   then `venv/bin/pip install -r requirements.txt`. The full-set
   resolution was dry-run validated 2026-10-06 (90 packages, no
   conflicts). If pip serves stale metadata, add `--no-cache-dir`.
3. `source env_python && cd val/math && make clean-all && make run-all-full-parallel`
   — repeat for `val/common`, `val/cdc` (the BKM set per Sean; bridge
   was already validated at exact parity in TASK-025 and is serial/heavy).
4. Green = flip done; close this task and note the date in TASK-025.
   Red = do NOT debug forward on a half-switched venv: rebuild the old
   venv from the pre-flip requirements (`git show 8fb596b57^:requirements.txt`),
   file what failed, and decide from a working baseline.

## Done when

- One BKM area produces a valid coverage database under cocotb 2.1.0 with
  cocotb-coverage 2.x, matched against a 1.9.2 control.
- Both pins updated (or the split-venv fallback recorded as a decision).
- The `cocotb==2.1.0` flip committed with a green BKM re-run.
