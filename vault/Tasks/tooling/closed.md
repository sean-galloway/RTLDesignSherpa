<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# Tooling tasks — closed (complete)

_None._

---

### TOOL-009: Python version mismatch breaks EVERY Verilator build on this box
**Priority:** P0 — blocks all simulation, and blocks TOOL-008 validation
**Status:** ✅ Closed 2026-07-23 — fixed and verified green (see Resolution)
**Owner:** Sean (decide the fix) / Claude (apply)

**Symptom:** every test fails at link time with
`undefined reference to Vtop::Vtop(char const*)`. Not an RTL or testbench
problem, and **not** caused by the TOOL-008 Makefile rewrite — it reproduces
under raw `pytest` with no make involved at all.

**The chain, each link verified by execution:**

1. `/usr/bin/python3` is a symlink to **python3.10** (3.10.12).
2. The venv was built from `/usr/bin/python3.11`, which on this box is
   **3.11.0rc1** — a release candidate, not a release (`venv/pyvenv.cfg`).
3. `cocotb_test/simulator.py:215` sets `PYTHONHOME = sysconfig prefix` for the
   simulator subprocess. Inside a venv that is the **venv** prefix (3.11).
4. Verilator's `share/verilator/include/verilated.mk:20` hardcodes
   `PYTHON3 = /usr/bin/python3` — baked in when Verilator was configured, so it
   is **3.10**.
5. Building `Vtop__ALL.cpp` runs that 3.10 interpreter with `PYTHONHOME`
   pointing at a 3.11 stdlib. It dies:
   `AssertionError: SRE module mismatch` (from `import re`).
6. The recipe is `... $^ > $@`, so the shell has **already truncated**
   `Vtop__ALL.cpp` before the interpreter fails. Result: a **zero-byte**
   amalgamation.
7. Empty `.cpp` -> 824-byte `Vtop__ALL.o` -> archive with no `Vtop` symbols ->
   the link errors above.

**Proof of the fix:** `make -f Vtop.mk PYTHON3=<venv>/bin/python3 Vtop__ALL.cpp`
produces a correct 522-byte file, and `test_amba_clock_gate_ctrl` then
**passes**. Nothing else was changed.

**Why it looks like a flaky/stale-build problem and is not.** `--reruns 3` and
xdist retries re-enter the same broken build dir and fail identically — the
five `*_results.xml` files in one `local_sim_build/` dir are that. `clean-all`
does not help: a fresh dir reproduces it 2/2. Do not chase this as a stale
artifact; see [[running-regressions]].

**Fix options, in preference order:**
- [ ] **Rebuild the venv on the interpreter `/usr/bin/python3` resolves to**
      (3.10.12), so `PYTHONHOME` and Verilator's hardcoded `PYTHON3` agree.
      Robust, survives a Verilator reinstall, no root needed. Confirm nothing
      in the stack actually requires 3.11 first.
- [ ] Or repoint `/usr/bin/python3` at 3.11 — needs root and changes system
      behaviour for everything else on the box.
- [ ] Or patch `verilated.mk:20` to `PYTHON3 ?= /usr/bin/python3` and export
      `PYTHON3` from `env_python` (make lets the environment win over `?=`).
      Cheapest, but it edits a file under `~/tools` that a Verilator reinstall
      silently reverts — if chosen, `bin/install_tools.sh` must apply it.

**Do not build a venv on a release candidate.** 3.11.0rc1 should not be the
base for anything; whichever option is chosen, pin a released interpreter.
Belongs with TOOL-004 — this is exactly the class of gap "validate the
bootstrap on a genuinely clean box" exists to catch, and the rebuilt
workstation shipped it.

**Resolution (2026-07-23):** rebuilt the venv on `/usr/bin/python3` (3.10.12) so
it matches the interpreter Verilator hardcodes. Three pins required Python
>=3.11 and now carry environment markers so one `requirements.txt` serves both
this Jammy box and Sean's 3.11 server:

| pin | >=3.11 | <3.11 |
|---|---|---|
| numpy | 2.3.4 | 2.2.6 |
| contourpy | 1.3.3 | 1.3.2 |
| Pint | 0.25 | 0.24.4 |

**Why 3.10 and not 3.11 on this box:** Ubuntu 22.04 (Jammy) ships python3.11
only as `3.11.0~rc1-1~22.04` — a release candidate. `/usr/bin/python3` is 3.10
and is what Verilator baked in. Sean's server is a later Ubuntu where
`/usr/bin/python3` already is 3.11+, which is why this never bit there. The bug
was never "3.11 is broken", it was the venv and Verilator disagreeing.

**numpy downgrade risk, assessed not assumed:** numpy is imported by exactly
one module in RDS-DV (= the `cocotb-framework` package),
`components/shared/memory_model.py`, and only via API stable since numpy 1.x
(`frombuffer`, `zeros`, `arange`, `append`, `any`, `sum`, `flatnonzero`,
`count_nonzero`, boolean masks). 2.3.4 -> 2.2.6 is a minor step inside 2.x, so
none of the 1.x->2.x breakage applies. Verified by running MemoryModel
write/read/access-map/expand under 2.2.6. The repo's other 17 numpy users are
`bin/dma_model/` analysis and plotting scripts, not the simulation path.

**Verified green after the fix:** `test_amba_clock_gate_ctrl` 1 passed, and
`make 'run-apb5_master*-gate'` -> 3 files / 9 passed at 7 workers, both through
the new TOOL-008 Makefile.

---

## TOOL-013 — Cohesive SKILLS strategy for the repo
**Status:** CLOSED 2026-08-09 (migrated from /TOOLING_TODO.md item 2, opened
2026-07-22; the work happened in the weeks between and the tracker never
caught up)

Wanted: repo-resident skills every agent/session discovers automatically,
replacing methodology scattered across CLAUDE.md files, bin/*.md how-tos and
fragile assistant memory. Proposed `.claude/skills/<name>/SKILL.md`.

**Verified done, and beyond the original list.** `.claude/skills/` exists and
carries every candidate skill from the proposal — doc-methods, kmaps,
uart-harness (sim and FPGA halves merged into one), hard-design, rds-dv-bfms,
filelists, review-rounds — plus the ones the model grew into: coverage,
formal, fsm-discipline, module-docs, rds-dv-axes, rds-dv-randomization,
regressions, signal-prefixes, tasks, test-review, doc-placement. The open
decisions resolved the way the vault settled them: skills are SIGNPOSTS
pointing at canonical handbook notes (vault/handbook/INDEX.md), method detail
lives in the handbook, GLOBAL_REQUIREMENTS.md stays the enforcement authority
(owner decision 2026-07-22, preserved). The "skill pointers must not rot"
verification wish is the one piece with no enforcement today — if that
becomes real work, open it fresh.

---

### TOOL-012: Burn down --blindspots, then make it a gate
**Status:** CLOSED 2026-08-28 (opened 2026-07-26, measured at `0928fb0b`)
**Priority:** was P2

Opened at 516 findings in three classes. Final state: **0, 0, and 2** -- the
two survivors are tracked as FORMAL-INTEG-COMMON-ORPHANS. The gate itself went
in long ago (`9d0a0c60`); this was the burn-down.

**Be honest about which of these was work and which was arithmetic.**

| class | 516-era | now | what actually happened |
|---|---|---|---|
| tests hand-listing sources | 128 | **0** | real burn-down. 128 -> 12 by earlier passes; the last 12 in `78506f35` -- nine genuinely converted to `get_sources_from_filelist` (plus six missing stub filelists created, since the stub variant runs at gate level), and three that were never hand-listed at all |
| `.sby` dead source paths | 387 | **2** | mostly NOT burn-down. The 387 counted `formal/**/config.sby`, which SymbiYosys GENERATES into every `<task>_prove/` and `<task>_cover/`; none are tracked. Fixed in `ecdf5a3e` to scan tracked files only. Two genuinely dead harnesses remain |
| unregistered filelist | 1 | **0** | `ddr2_char_macro.f` registered |

So the headline "516 -> 2" overstates it. One class was burned down properly,
one was largely a measurement error in the checker, and the checker also
**miscounted the class it was best at**: three of the last twelve tests were
false positives, flagged for the string `verilog_sources = [` when that was a
merge accumulator in a test that already used filelists for its RTL and merely
appended its own `tb_*.sv` harness. That detector now parses with ast and
judges only expressions that flow into `verilog_sources`.

**The lesson worth keeping** is the one this task was created to make, turned on
itself: a check that cannot be trusted to count is as bad as no check. The
`.sby` scan reported REGRESSED locally and PASS in CI for identical commits; the
test scan called three correct tests broken. Both were mutation-tested after
fixing -- break it, see it caught, restore it, see it clear -- which is the
standard the rest of this gate should be held to.

See [[filelists]], TOOL-014 for the three gate blind spots fixed alongside.

### TOOL-015: `--reruns 3` re-rolls the seed, so a seed-exposed RTL bug retries until it passes

**Status:** FIXED 2026-09-07, commit 071711af. One repo-root `conftest.py`
derives each test's seed from sha256(session base, node id), so a retry repeats
the run it is retrying. The 338 wrappers were not touched -- they already read
SEED from the environment.

Verified separately: reruns reuse the seed (3 attempts, all 55072, also under
xdist); `SEED=777` still wins; different tests differ; a new session re-rolls
so exploration survives; the value reaches the simulator (conftest computed
37611, sim log shows SEED=37611); collection unaffected in nine areas.
FULL runs after the change, 0 reruns: math 401, common 945, cdc 352, amba 1728.

`RDS_SEED_BASE` replays a whole run and the base prints in the pytest header.
The first attempt at that was WRONG in a way worth recording: it read
PYTEST_XDIST_TESTRUNUID, which the controller does not have when the header
renders, so it printed a base no worker used and "replaying" produced a third
seed space. A reproduction handle that does not reproduce is worse than none.
Caught by testing the replay rather than reasoning about it.

`--reruns 3` deliberately left in place, per the note below: it is also
absorbing genuine infrastructure noise, and the budget can now be judged from
evidence, because a seed-exposed failure will fail all four attempts and be
reported with a recoverable seed.

**The mechanism.** Every test wrapper picks its seed like this (338 files, one
uniform pattern):

```python
seed = int(os.environ.get('SEED', str(random.randint(0, 100000))))
```

and `make/tests.mk:70` runs every area with `PYTEST_RERUNS ?= --reruns 3
--reruns-delay 1`. `pytest-rerunfailures` re-executes the whole wrapper on a
retry, so `random.randint` is called AGAIN and the retry runs a **different
seed**. A failure that depends on the seed therefore gets up to three fresh
chances to not happen, and the run reports `401 passed, 1 rerun`.

The failing seed is not recorded anywhere. The per-test log is named for the
test and worker (`logs/test_..._func_FULL_gw29.log`), so the passing retry
**overwrites** the failing attempt's log on the same worker. `--tb=short`
prints no traceback for a rerun that eventually passes. The evidence is gone in
both places.

**Observed 2026-09-07.** `val/math` FULL: `test_math_fp8_e4m3_fma[params1]`
reran once and passed; the immediately preceding FULL run of the same suite
passed it outright. Two runs, two seeds, two outcomes, and no way to reproduce
the failing one. That is indistinguishable from a real intermittent RTL defect,
which is why it cannot be waved off -- see [[feedback_no_flaky_dismissal]].

**Why this is worse than a plain flake.** A rerun that passes is not evidence
of a flake; it is the ABSENCE of evidence. Randomised stimulus exists to find
bugs the directed tests miss, and a retry-until-green policy is precisely the
policy that discards those finds. The suite is doing the search and then
throwing away the hits.

**The fix is small and central, because the indirection is already there.**
Every wrapper reads `os.environ.get('SEED', ...)`, so nothing needs to change
in the 338 files. A session-scoped autouse fixture in each area's existing
`conftest.py` (`val/{math,amba,cdc,common}/conftest.py` already exist) can
assign a seed per test NODEID and export it:

```python
@pytest.fixture(autouse=True)
def _pin_seed(request):
    # Same nodeid -> same seed, so a rerun repeats the run it is retrying
    # instead of rolling a new one. Fresh per session, so randomised
    # exploration across runs is unaffected.
    key = request.node.nodeid
    os.environ['SEED'] = str(_session_seeds.setdefault(key, random.randint(0, 100000)))
```

With that, a seed-exposed failure fails all four attempts, gets REPORTED, and
its seed is in the log where `SEED=<n> pytest <test>` reproduces it.

**Do not** simply drop `--reruns`: it is also absorbing genuine infrastructure
noise (a killed worker, a busy machine), and removing it without the seed fix
trades a silent hole for a noisy one. Pin the seed first, then judge how much
of the rerun budget is still earning its keep.

**Also worth fixing while in here:** include the seed in the per-test log
filename, or refuse to overwrite a log from a failed attempt, so the failing
run's log survives its own retry.

**Related:** [[silent-fallbacks]] rule 11, [[seeds-and-determinism]],
[[running-regressions]].
