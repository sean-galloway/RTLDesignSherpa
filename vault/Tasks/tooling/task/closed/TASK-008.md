# TASK-008: One gate that runs filelist_registry --check and --audit

> Migrated 2026-09-27 from `vault/Tasks/tooling/closed.md` as **TOOL-003** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P2 -> P3 (re-scoped)
**Status:** Closed 2026-09-23. The last two items landed today.
The failure message now names the destination directory
(`uncovered module: X -> add a .f under <area>/filelists`), and the `[exempt]`
ledger is ratcheted against `bin/filelist_exempt_baseline.json`: `--check`
prints an exempt count per area and fails when one GROWS, with
`--update-exempt-baseline` to re-baseline deliberately. Proven non-vacuous by
tampering the baseline (pumice 2 -> 0), getting rc=1 and the FAIL line, then
restoring to rc=0.
**Owner:** TBD

Shared deliverable for COMMON-010 and AMBA TASK-026 — build it once here rather
than twice in the areas.

**The premise below was true when filed and is FALSE now** -- kept because the
re-scope only makes sense against it. It read: "`--check` is currently run by
nothing: not the pre-commit hook, not CI (`track-clones.yml` is the only
workflow), not a Makefile target."

Measured 2026-09-16, all three clauses are wrong:

- `.github/workflows/filelist-checks.yml` runs `--check`, `--audit` and
  `--blindspots --ratchet` as hard gates on push, PR and dispatch, plus
  `check_doc_examples.py` and `check_test_dut_family.py`.
- `.git/hooks/pre-commit` runs the same three locally, gated on staged
  `.f/.sv/.svh/.sby/.toml` or `test_*.py` -- a deliberate superset of the
  ".sv or .f" this entry asked for, because `.sby` and `test_*.py` are the
  blindspot carriers.

- [x] Add `--check` to the pre-commit hook, scoped. **Done**, and scoped wider
      than asked (see above).
- [x] Add `--audit`. **Done** -- the hook loops `for check in --check --audit`,
      and CI runs it as its own step.
- [x] Decide whether a CI workflow is also wanted. **Done, decided yes.**
- [ ] PARTIAL -- make the failure message name the offending module **and the
      area's `filelists/` dir**. `cmd_check` prints `uncovered module: {m}` and
      the area name, but never the directory the `.f` belongs in, so the fix
      still is not obvious without reading the tool. One f-string.
- [ ] NOT DONE, and this is the substantive half -- fail (or delta-report) when
      the `[exempt]` ledger GROWS. `cmd_check` line ~436 is
      `missing = sorted(m for m in declared - covered if m not in exempt)`, so
      an exempt module is silently subtracted and a new exemption passes every
      gate. `--blindspots --ratchet` does NOT cover this: it ratchets
      unregistered `.f`, hand-listed tests and dead `.sby` paths, a different
      class. Validating [[TASK-026]] on 2026-09-16 required reading the ledger
      by hand for exactly this reason.

**Gotcha to preserve:** `--check` exits PASS when `declared - covered - exempt`
is empty, so a gate that only inspects the exit code will not notice the
`[exempt]` ledger growing. Either fail on new exempt entries or report the
counts. See [[filelists]].

---

---
