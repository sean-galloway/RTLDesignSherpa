# TASK-003: Two real gaps in the RDS-DV arbiter BFM

> Migrated 2026-09-27 from `vault/Tasks/tooling/open.md` as **TOOL-007** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P2
**Status:** CLOSED 2026-09-27 -- both gaps fixed in RTLDesignSherpa-DV 784f905 (pushed)
**Owner:** tooling session (Claude)

Found while fixing COMMON-012. Both belong in the RTLDesignSherpa-DV repo, not
here; file them there and reference this task.

- [x] **`ArbiterCompliance.analyze_round_robin_compliance()` is a stub.** It
      returns a hardcoded `{'rr_efficiency': 1.0, ...}` regardless of the
      observed grant sequence — see `components/shared/arbiter_compliance.py`.
      It is the one check whose name promises to catch a rotation defect, and
      it cannot. A clean report from it is not evidence of anything. Either
      implement it against the grant history the monitor already records, or
      make it return `{'status': 'not_implemented'}` so callers cannot mistake
      it for a pass. `detect_burst_behavior()` is stubbed the same way
      (`bursts_detected: 0` hardcoded).
- [x] **`ArbiterMaster` cannot saturate via a profile.** Its
      `_setup_default_profiles` defines a private set (`default`, `fast`,
      `slow`, `disabled`, `manual`) that is not wired to `FlexConfigGen`, whose
      `DEFAULT_PROFILES` already contains `backtoback` = `[(0,0)]` = zero delay.
      Even `fast` carries a 1-3 cycle `inter_request_delay`, so all-clients-up
      never sustains and arbiter tests silently under-stress. Workaround in use:
      `force_client_request(c, enable=True)`. Wire the shared catalogue in, or
      add a saturating profile.

Why this matters beyond tidiness: the combination of these two is what let a
round-robin arbiter that starved half its clients pass its own testbench. See
[[randomization]].

---

## Closure (2026-09-27)

Fixed in the DV repo, commit `784f905` on `main` (pushed; `ruff check src/`
clean, 1504 unit tests pass with `PYTHONPATH=$DV/src`):

- `components/shared/arbiter_compliance.py`: `analyze_round_robin_compliance()`
  now scores the recorded grant history -- `rr_checks` / `rr_violations`
  counters are incremented in both the ACK and no-ACK grant paths, efficiency
  is violations over checks, and zero checks reports `status: 'no_checks'`
  rather than a silent 1.0 (a verdict needs a count, see
  [[checker-verdict-needs-a-count]]). `detect_burst_behavior()` is real:
  consecutive same-client grants above the burst threshold are counted from
  the same history.
- `components/shared/arbiter_master.py`: `ArbiterMaster.catalogue_client_profiles()`
  exposes the shared `FlexConfigGen` `DEFAULT_PROFILES` (so `backtoback` is
  reachable), and a `saturate` profile holds every enabled client's request
  high with zero inter-request delay. `force_client_request()` stays as the
  per-client override.
- `tests/unit/test_arbiter_compliance.py`: +6 tests -- a starving rotation
  now FAILS the round-robin check, a fair one passes, bursts are detected, the
  zero-check case reports `no_checks`, and the saturate profile sustains
  all-clients-up.

Not done here: the main repo's venv still carries an older editable install of
CocoTBFramework than the DV checkout, so main-repo arbiter tests see the new
API only after `pip install -e $DV` in the venv. That refresh is the owner's
call (it changes every peer session's framework at once) and is noted, not
performed. The handbook gap list in [[randomization]] should drop these two
entries when the venv is refreshed.
