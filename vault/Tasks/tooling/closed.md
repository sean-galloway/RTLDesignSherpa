<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# Tooling tasks — closed (complete)

## TOOL-008: Redo the Makefiles from scratch
**Priority:** P1
**Status:** Closed 2026-09-20 — Sean signed off. R1-R4 all hold, validated
by real regressions, not by structure.

**Closed with two items carried forward, deliberately not buried:**
1. `Genesys2/stream/rtl/bridges/dv/tests/Makefile` (3 hardcoded `-n`) and the
   pumice `dv/tests` Makefiles were outside this sweep. Neither is a defect in
   what landed; both need the same four-line treatment when their owners get
   to them.
2. c74e22c76 stopped reading `coverage_workers` (24) and `coverage_reruns`
   (5/2), so a coverage run now uses the derived width with 3 reruns. The
   intent was memory headroom during instrumented runs; `GB_PER_WORKER=4`
   restores it host-aware rather than pinning a number. Seven other toml keys
   are now read by nothing. **Still an open decision** — tracked here rather
   than lost, because the task that created it is closing.
**Owner:** Sean (spec + validation) / Claude (implementation)

**Where it actually stands (2026-09-18).** The proof of concept this entry used
to describe is gone: there is no `Makefile.poc` anywhere, and `val/amba/Makefile`
is the 5-line leaf (the 2074-line original is retired). `make/tests.mk` is live
at 312 lines and **26 Makefiles** include it across `val/`, `projects/components/`,
`projects/fpga-systems/` and `projects/asic-trials/`.

| requirement | state |
|---|---|
| R1 derive the thread count | DONE — `JOBS = min(nproc, MemGB/GB_PER_WORKER)`; derived **48** on a 48-core/188 GB host, **7** on the 8-core box |
| R2 one target grammar | DONE — `run-<all\|testglob>-<gate\|func\|full>[-serial\|-parallel][-waves]`, generated not enumerated |
| R3 discover by glob | DONE — `TESTS := $(sort $(wildcard test_*.py))`; a new test is runnable the moment it lands |
| R4 one master, 4-line leaves | DONE — leaves are 4-5 lines; `val/Makefile`, `projects/components/Makefile` and the per-component dispatchers forward and carry no test logic |

**The blocker this entry named is satisfied — by runs, not by structure.**
A whole-area FULL regression went through `clean-all` + `run-all-full-parallel`
on 2026-09-18: 861 cells, `fub` 123 passed, `macro` 680 passed + 3 skipped,
`top` 52 passed + 3 xfailed. And `make test-val-common-gate` — a generated
target — ran 77 passed in 37 s through the delegated path.

**The last R1 hole was the generated targets themselves** (c74e22c76).
`test_targets.mk` hand-built `cd <dir> && pytest ... -n 48 test_*.py` for every
environment, re-implementing tests.mk and pinning the worker count. The
generator now emits `$(MAKE) -C <dir> run-all-<level>-<mode>`: 113 target names
unchanged, hardcoded `-n` 59 -> 0, raw `cd` recipes 93 -> 0, delegations 8 -> 101.

**What is left, and why it is not closed:**
1. Sean's sign-off — the Done-when is his validation, not a session's.
2. Two areas outside this sweep: `Genesys2/stream/rtl/bridges/dv/tests/Makefile`
   (3 hardcoded `-n`, stream is owned elsewhere) and the pumice `dv/tests`
   Makefiles (skipped by standing instruction).
3. A decision c74e22c76 forces: delegation stopped reading `coverage_workers`
   (24) and `coverage_reruns` (5/2), so coverage now runs at the derived width
   with 3 reruns. The intent was memory headroom during instrumented runs.
   `GB_PER_WORKER=4` would restore it host-aware rather than pinning 24.
   Seven other toml keys (`pytest_flags`, `test_pattern`, `reruns`,
   `reruns_delay`, `coverage_extra_env`, ...) are now read by nothing; their
   values are reproduced by tests.mk, which is why delegating was safe, but
   unread config rots and should be deleted once (3) is decided.

**Worker-count rule as implemented:** `JOBS = min(nproc, MemTotalGB /
GB_PER_WORKER)`, `GB_PER_WORKER ?= 2`, both overridable
(`make JOBS=16 ...`). The memory ceiling is deliberate and is the one that
would actually have prevented the machine death — Verilator elaboration is
RAM-hungry and swap is what makes a box stop responding; a cores-only rule
would not have caught it. Open to being reduced to cores-only if Sean prefers.

**History.** Sean wrote an extensive design for this. That document was never
committed here and did not survive the workstation loss on 2026-07-23 — not in
the tree, not in any local or remote branch, not in reflog/stash/dangling
objects, not in any surviving session transcript. A prior session promised to
file this task and did not. The requirements below were **re-dictated by Sean on
2026-07-23** after the loss; they are his words paraphrased, not reconstructed by
inference. If the original doc resurfaces, reconcile against it — it was longer
than this.

---

### R1 — Every Makefile figures out its own thread count. No hardcoded numbers.

**This is the requirement that killed a machine.** The hardcoded worker counts
assume a big host; on a smaller one they oversubscribe until it dies. Sean had
to hard-kill the workstation on 2026-07-23 because of this.

Measured 2026-07-23 (host `nproc` = **8**):
- **`-n 48` is hardcoded in 28 files.** `test_targets.mk` alone has **70**
  occurrences; `env_python` has 2; each of `val/{amba,common,integ_amba,
  integ_common}/Makefile` and ~20 `projects/**/dv/tests/**/Makefile` have 1-2.
  On this 8-core box that is a **6x oversubscription** by default.
- Other files pick different numbers with no rationale: `-n 24`, `-n 2`,
  `PYTEST_WORKERS := 8` (stream `performance_tests/Makefile`).
- Exactly **one** place does it right and nothing else copies it:
  `projects/components/Makefile:58-59` —
  `FAST_JOBS ?= 4` / `FAST_WORKERS ?= $(shell echo $$(( $$(nproc) / $(FAST_JOBS) )))`.
- The number is also baked into non-Makefile files that must be swept with them:
  `bin/aggregate_test_results.py`, and the docs
  `vault/handbook/dv/test-runner.md` (2), `projects/components/MAKEFILE_GUIDE.md`,
  `projects/components/MAKEFILE_HIERARCHY.md`.

Derive from `nproc` in ONE place, overridable by env var. Remember these are
Verilator sims — each worker is a compile+sim process, so the right divisor is
not necessarily 1-per-core; whatever the rule is, it lives in the master
Makefile and nowhere else.

### R2 — One consistent target grammar, everywhere.

```
make run-<all|testroot>-<gate|func|full>[-serial|-parallel][-waves]
```

- **testroot** is the test file with `test_` and `.py` stripped:
  `test_grey2bin.py` → `make run-grey2bin-func`.
- `all` means every test in scope for the Makefile you are standing in.
- **The mode and waves suffixes are OPTIONAL** (Sean, 2026-07-23: "serial is
  optional like waves"). Bare `run-<x>-<level>` is parallel without waves, so
  the common case types shortest. This also resolves the earlier open question
  about the dictated grammar ending in the serial|parallel axis twice — it is
  one optional mode suffix plus one optional waves suffix, matching the
  `-gate` / `-gate-waves` / `-gate-serial` shape `test_targets.mk` already uses.
- Six variants per level, all generated, none enumerated: bare, `-parallel`,
  `-serial`, `-waves`, `-parallel-waves`, `-serial-waves`.
- Today the targets are hand-written and combinatorial instead —
  `val/amba/Makefile` is **2074 lines / 229 targets**, `val/common/Makefile`
  **1245 / 131**, root `Makefile` **976 / 83**, `projects/components/Makefile`
  **613 / 35**. Adding a module means hand-editing several targets across
  several files and nothing checks that you did.

### R3 — Discover tests by globbing. Do not enumerate them.

Targets are generated from globbing `test_*.py`, so a new test is runnable the
moment it lands. This is what makes R2 maintainable and kills the combinatorial
hand-written target lists.

### R4 — One master Makefile; every other Makefile is ~4 lines.

All logic lives in the master (include/`.mk`). A leaf `Makefile` in
`val/common/`, `projects/**/dv/tests/fub/`, `macro/`, `top/` etc. sets its few
locals and includes the master. Today those leaf Makefiles are "completely
different" from each other across `common/`, `amba/`, and the `projects/` areas
— same job, divergent implementations, which is how the thread handling drifted
in the first place.

---

**Measured state of the problem (2026-07-23), as the starting evidence:**
- **124 Makefiles** in the repo (excluding `venv/`): 36 under
  `projects/components/`, 18 under `projects/NexysA7/`, 60 under `formal/`,
  5 under `val/`, plus the 3-tier roots.
- The regression Makefiles are **enormous and hand-maintained** — line/target
  counts under R2 above.
- The hand-written target set is combinatorial — every protocol crossed with
  `-parallel`, `-gate`, `-func`, `-full`, plus per-module variants
  (`run-apb5-master`, `run-apb5-slave`, `run-apb5-monitor`, `run-apb5-cg`,
  `run-apb5-cdc`, `run-apb5-stub`, ...). This is exactly what R2+R3 replace.
- The `fub/` / `macro/` / `top/` split repeats across `dmas/stream`,
  `dmas/rapids`, `pumice`, `misc`, `timing_characterization` — each with its own
  divergent Makefile doing the same job. These are the R4 four-liners.
- The existing three-tier description lives in
  `projects/components/MAKEFILE_HIERARCHY.md` and `MAKEFILE_GUIDE.md`
  (both dated 2025-10-24, pre-dmas-reorg). Per the handbook rule these are
  methodology living next to code and should end up as handbook notes —
  coordinate with TOOL-002.

**Related work already tracked, do not duplicate:**
- TOOL-003 wants a gate running `filelist_registry --check/--audit`; a Makefile
  rewrite is the natural home for it, since the filelists are what a
  regenerated target set would key off.
- [[test-runner]] and [[running-regressions]] document the current
  Makefile → pytest → cocotb_test.run → Verilator stack and the
  `REG_LEVEL` vs `TEST_LEVEL` distinction. Any rewrite must keep those
  semantics or update both notes in the same change.

---

## TOOL-009: Python version mismatch breaks EVERY Verilator build on this box
**Priority:** P0 — blocks all simulation, and blocks TOOL-008 validation
**Status:** Closed 2026-07-23 — fixed and verified green (see Resolution)
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

## TOOL-012: Burn down --blindspots, then make it a gate
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

## TOOL-015: `--reruns 3` re-rolls the seed, so a seed-exposed RTL bug retries until it passes

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

<!-- Moved from vault/Tasks/amba/ 2026-09-14: a tooling task, filed under amba -- RENUMBERED to TOOL-018 on arrival, because tooling already has a DIFFERENT live TOOL-014 (Scripts book link rot) -->
## TOOL-018 — the filelist gate was blind outside registered areas, to +incdir+, and to its own build output
**Status:** CLOSED 2026-08-28 (opened same day)
**Renumbered 2026-09-14:** filed as TOOL-014 in `amba/closed.md`, where that number was free. Moving it to tooling put it against a DIFFERENT live TOOL-014 (Scripts book link rot), so it took the next free tooling number. The area is the ID namespace.
**Priority:** was P2 — CI was green with a half-finished rename on main

CI failed on `--check` with 7 broken `-f` targets: 35036222 renamed the monbus
group filelists and committed the rename, but the consumers were fixed in the
working tree only (cd954548). Three blind spots let that happen; all fixed in
ecdf5a3e, each mutation-tested.

1. **`--check` SKIPPED every area with no `rtl_roots`.** Ten areas -- the
   NexysA7 boards, Genesys2, val -- declare `filelist_dirs` but no roots, and
   `cmd_check` did `if not roots: continue`. They were not orphans either, so
   `--blindspots` missed them too. Coverage is meaningless without roots;
   reference integrity is not. They are now resolved for broken refs.
2. **`+incdir+` was never checked.** Ten filelists searched
   `rtl/common/includes`, a directory that never existed (3873c812).
3. **`--blindspots` counted SymbiYosys BUILD OUTPUT.** It walked
   `rglob("*.sby")`, which finds the `config.sby` sby generates in every
   `<task>_prove/` and `<task>_cover/`. So the count depended on whether you
   had run formal: 1564 locally vs 2 clean, against a baseline of 387 --
   REGRESSED locally, PASS in CI, same commit. Now tracked-only.

**It took three commits to finish one rename** (cd954548, 7b1eac2b, 4c4ead1b)
because the gate could only see a third of the tree. The last one was found by
the fixed gate itself on a fresh clone -- the intended demonstration.

**Widening --check exposed three under-resolutions**, fixed rather than muted
since each would have been a false failure:

  * Relative entries resolve against the filelist's PARENT too. 41 real
    timing_characterization files would have read as missing.
  * **Flow variables are MULTI-VALUED, and this corrects an earlier wrong
    call.** `STREAM_CHAR_ROOT` was pinned in ROOT_VARS to flows-stream-bridge,
    but flows-stream-bridge, flows-stream-monitor and Genesys2/stream each
    `export STREAM_CHAR_ROOT := $(SELF_DIR)`; FRAMEWORK_ROOT likewise has three
    values. `_scan_flow_roots()` now harvests the real values from the
    Makefiles that export them, so adding a flow cannot silently un-cover it.
  * A target inside a git-ignored path is supplied externally.
    `flows-idma-bridge/external/` is gitignored and bender-populated; its eight
    include dirs would have made the gate permanently red for a condition no
    commit can fix.

**Mutation-tested**, because a gate that cannot fail is not a gate: breaking a
`-f` in an rtl_roots=0 area and adding a dead `+incdir+` each produce exit 1
with the right message; a dropped-in generated `config.sby` is not counted
while the two TRACKED dead .sby paths still are (positive control that the fix
did not just blind the check); all restored -> exit 0.

Baseline relowered to honest numbers: dead_harness_paths 387 -> 2,
hand_listed_tests 125 -> 12, unregistered_filelists 1 -> 0.

**Still open, deliberately:** `--check` does not verify `+incdir+` reachability
for flow-scoped vars it cannot enumerate, and `--unrolled` exits 1 (pre-existing,
not a CI gate). `hand_listed_tests` at 12 remains TOOL-012's backlog.

---

---

---

---

## TOOL-017: `lint-<component>` is advertised but cannot run for two areas
**Priority:** P3
**Status:** Closed 2026-09-23. The work below was done on 2026-09-15 and the
entry then bounced back to open on 09-16 because its HEADER still said "Not
Started" -- the closure record was in its own body, eight paragraphs down.
Re-verified today by running the gate, not by reading it: `lint-retro_legacy_blocks`
84 modules, `lint-apbx-xbar` 21, `lint-misc` 56, each elaborated as its own top,
all exit 0, and COMPONENTS carries the hyphenated `apbx-xbar`.
Original text, true when filed:
`retro_legacy_blocks` has an `rtl/Makefile` but NO `lint-all` target, and
`apbx_xbar` has no `rtl/` directory at all, while the template at
`projects/components/Makefile` delegates unconditionally to
`$(MAKE) -C $(1)/rtl lint-all`.
**Owner:** TBD

`projects/components/Makefile` generates a lint target per component and
advertises them in `make help`:

    make lint-retro_legacy_blocks  Lint Retro Legacy Blocks RTL

Both of these fail immediately, measured 2026-09-14:

    $ make lint-retro_legacy_blocks
    make[1]: *** No rule to make target 'lint-all'.  Stop.
    make: *** [Makefile:463: lint-retro_legacy_blocks] Error 2

    $ make lint-apbx_xbar
    make[1]: *** apbx_xbar/rtl: No such file or directory.  Stop.
    make: *** [Makefile:463: lint-apbx_xbar] Error 2

The template at `Makefile:456` delegates to `$(MAKE) -C $(1)/rtl lint-all`.
stream, rapids, bridge and converters each have an `rtl/Makefile` providing
`lint-all`; **retro_legacy_blocks and apbx_xbar do not**, and apbx_xbar has no
`rtl/` directory under that name at all.

**Why it matters rather than being cosmetic.** A gate that cannot run is not a
gate, and this one is advertised in `help`, so the natural assumption is that
the area is linted. It is not: [[RLB-015]] sat unverified for days partly
because the reporter concluded "retro_legacy_blocks has no lint target, so
nothing is measured" -- the right conclusion from the wrong premise. The area
IS lintable; every block has a working top filelist and
`verilator --lint-only -Wall --timing -f <filelist>` runs clean today.

**Fix options, in order of preference:** give the two areas an `rtl/Makefile`
with a `lint-all` that loops their top filelists (the sweep in RLB-015's
closure is a working prototype); or have the template discover filelists
directly and drop the per-area Makefile requirement; or, at minimum, stop
advertising targets that cannot run.

**SAME ROOT CAUSE, WORSE SYMPTOM, found 2026-09-14: the whole component
regression cannot run either.** `projects/components/Makefile` line 31 lists
the component as `apbx_xbar`, but the directory was renamed to the hyphenated
house style and is `apbx-xbar` on disk. It is the FIRST entry in `COMPONENTS`,
and the loop at `Makefile:259` ends each iteration with `|| exit 1`, so:

    $ make clean-all && make run-all-full-parallel
    ==> Testing apbx_xbar (FULL, 48 workers)
    make[1]: *** apbx_xbar/dv/tests: No such file or directory.  Stop.
    make: *** [Makefile:259: test-all-full-parallel] Error 1

That aborts before a single test of ANY component executes. So the documented
whole-repo command -- `make clean-all && make run-all-full-parallel`, which is
the standing instruction for every area -- has been exiting 2 without testing
anything, and the failure is 3 lines into a long log where it reads like
progress. It affects all six `test-all-*` targets, which share the loop.

**FIXED 2026-09-14** (Sean: "I fixed the apbx-xbar a couple of weeks ago.
That is the correct reference" -- the hyphenated directory is canonical, so
the Makefile was simply the stale side).

The history is a two-step rename that half-landed. `f28581b3d`
("refactor(apbx_xbar): rename apb4_xbar -> apbx_xbar", 2026-08-12) touched the
Makefile; `95f7006fc` ("...+ hyphenated dir", the SAME DAY) renamed the
directory to `apbx-xbar`. The Makefile kept step 1's name and was never
advanced to step 2b's, so `COMPONENTS` has pointed at a path that stopped
existing hours later. An earlier note here blamed f28581b3d for the rename;
that was wrong -- f28581b3d is the commit that was left BEHIND by it.

Fix applied: `apbx_xbar` -> `apbx-xbar` in `COMPONENTS`, plus the matching
`make lint-apbx_xbar` help line (the `lint-$(1)` template derives its target
name from COMPONENTS, so the advertised name moves with it). Only PATH
references changed -- the SystemVerilog modules stay `apbx_xbar_*`.

**The lint half of this entry stays OPEN.** `lint-apbx-xbar` now resolves the
path but still fails, for the separate reason above: apbx-xbar has no
`rtl/Makefile` providing `lint-all`. Same for retro_legacy_blocks.

Same lesson as the lint half: a gate that cannot run is not a gate. This one
additionally reported a non-zero exit that is easy to read as "the suite ran
and something failed" rather than "nothing ran at all".

**CLOSED 2026-09-15 — and the scope was SIX areas, not two.**

The entry named retro_legacy_blocks and apbx_xbar. Measuring every component
found four more, each broken differently, which is why a survey beat reasoning
from the template:

| area | what was actually wrong | now |
|---|---|---|
| retro_legacy_blocks | no `rtl/Makefile` at all | PASS, 84 modules |
| apbx-xbar | had a Makefile; `verible` target died on a shell syntax error | PASS, 21 modules |
| misc | no `rtl/Makefile` | PASS, 57 modules |
| pumice | no `rtl/Makefile` | PASS, 52 modules |
| stream | Makefile referenced `filelists/stream_all.f`, which never existed | PASS, 76 modules |
| rapids | same, `filelists/rapids_all.f` | PASS, 69 modules |
| converters | ran, but `|| true` per file and no `--top-module` — gated nothing | PASS, 65 modules |
| bridge | already a real gate (filelist-driven, `--top-module`, waivers) | left alone |

**The fix was not new lint logic.** `rtl/make/area.mk` already did exactly what
this entry asked for, and the four `rtl/` areas use it through a four-line
Makefile. Each component got the same four-line Makefile plus the
`filelists/<area>_all.f` master that `area.mk` (and stream's and rapids' own
Makefiles) had always expected. The 180-to-295-line per-area Makefiles are gone.

Verified per area with `make -C projects/components lint-<component>`; the
counts above are modules linted each as its own top.

**`area.mk` needed one change**, because it looked for a module's own filelist
only at a flat `filelists/<mod>.f`, which never matches an area that nests them
(`gpio/filelists/`, `filelists/core/`, `filelists/top/`). It now falls back to a
recursive search, flat-first so existing areas are unchanged. Proven against a
baseline captured BEFORE the edit: common 218, cdc 20, math 174, amba 402,
exit 0 — identical after, with per-module resolution now also working
(46/14/172/149 via own filelist).

**Three defects fell out of having a gate that actually runs:**

1. **An RTL bug in `axi4_slave_rom`** (misc). It had no ROM size parameter and
   derived one from the whole address space -- `ROM_ADDR_WIDTH = AXI_ADDR_WIDTH
   - $clog2(BYTES_PER_WORD)` = 29, so `2**29` entries, ~34 Gbit at 64-bit data.
   Verilator refuses to elaborate it ("vector of over 1 billion bits") and no
   flag suppresses it -- `--max-num-width` caps number width, not array depth.
   Nothing in the repo instantiates the module or overrides that width, which is
   why nobody noticed: the old per-file gate never elaborated anything. Fixed by
   giving the ROM a real `ROM_ADDR_WIDTH` parameter (default 12) and indexing it
   from the low address bits.

2. **`filelist_registry.py` audited its own generated output.** `area.mk` writes
   a flattened filelist to `<area>/rtl/lint_reports/` on every run, and
   `area_filelists()` did a bare `rglob("*.f")` with no tracked-file filter.
   retro_legacy_blocks declares the whole `rtl/` tree as `filelist_dirs`, so the
   auditor picked that artifact up; a flattened list hand-lists every source by
   definition, so `--audit` reported 29 cross-area sources and the pre-commit
   hook blocked EVERY commit until the untracked file was deleted -- a red gate
   no commit could fix. Now filtered through the existing `_git_ignored()`, the
   same rule `--blindspots` already used ("if git does not track it, it is not
   ours to register"). Verified with the artifact PRESENT, not merely deleted.

3. **`flatten_filelist.py` had no cycle guard.** A filelist that `-f` includes
   itself recursed until `RecursionError`, naming neither the file nor the
   cycle. That is easy to write by accident -- generate a master by globbing its
   own directory and it includes itself, which is exactly what I did to misc.
   It now exits 2 naming the chain.

**The top-level `Makefile` carried a third, worse copy of this defect** and was
fixed too: all ten project lint targets ended `|| true` so none could fail, each
was wrapped in a `[ -f .../Makefile ]` guard that printed "not found" and then
exited 0, `lint-apbx_xbar` still pointed at the pre-rename `apbx_xbar/` path,
and `lint-shims`/`lint-hive` named areas that do not exist. A target that
reports success for a missing area is worse than one that errors.

**Bridge was NOT converted, and should not be.** Its Makefile is a genuine
gate -- it loops its filelists, lints each with `--top-module`, counts failures
and carries real lint waivers -- so converting it would have thrown away the
waivers to make it resemble the others. It is slow (53 filelists, each flattened
then linted, ~7 min) and buffers into its own log, so it looks hung from the
outside. It is not; I killed it twice on that mistaken reading before probing at
the right level, which is the lesson: a make with no visible children is not
evidence of a hang until you have walked down to the level that would show them.

**But bridge WAS broken, in a fourth way, and it was hiding behind the same
`|| true` this task removed.** `make -C projects/components lint-all` still
exited 2 after every area passed, because `lint-all = verilator verible` and
bridge's `verible` recipe died with `/bin/sh: Syntax error: ";" unexpected`.

Cause: these Makefiles `-include $(REPO_ROOT)/makefiles/common.mk` and **that
file does not exist** -- there is no `makefiles/` directory in the repo, and
`print_success`/`print_warning` are defined nowhere. `-include` is silent by
design, so every `$(call print_success,...)` expanded to EMPTY. On its own
recipe line that is harmless, which is why nobody noticed; inside a continued
shell block it leaves a bare `;` between `cat ...;` and `else`, and the shell
refuses to parse it. So bridge's verilator half passed, printed its tick, and
the area still returned 2.

The same defect sat in **delta**, and only became visible once the top-level
`|| true` came off -- removing the mask is what turned a latent break into a
failing target. Fixed in both by replacing the four in-shell `$(call print_*)`
calls per file with plain `echo`s; the calls left on their own recipe lines are
harmless and were not touched. Verified: bridge `verible` exit 0, delta
`lint-all` exit 0, and no in-shell `$(call print_*)` remains anywhere.

apbx-xbar had this too -- it is why `lint-apbx-xbar` failed at
`Makefile:49: verible` rather than for the reason this entry originally
recorded -- but its Makefile was replaced wholesale, so the bug went with it.

---

---

## TOOL-003: One gate that runs filelist_registry --check and --audit
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

## TOOL-014 — Scripts book link rot + DOCUMENTATION_INDEX refresh
**Status:** Closed 2026-09-23 -- stale on every clause, and the remainder fixed.
Measured today: `_wavedrom_svg` and `puml_img` appear NOWHERE in the tree (those
pages were repointed at some earlier pass), and the "18 references" in
wavedrom_troubleshooting.md are 3 FENCED examples plus prose paths -- the link
gate excludes fences precisely because they are written relative to the page
being generated. Its 8 real links all resolve.
Two genuinely broken links did exist, in md_to_docx.md, and were exactly what
this entry predicted ("illustrative snippets; possibly fine as-is, mark as
examples"): line 56 documenting `![title](diagram.json)` and line 407
documenting `[Title](path/file.md)` -- markdown syntax being DESCRIBED, which
the checker read as links to follow. Both are now inside backticks, so the
inline-code exclusion covers them. Scripts book: 223 resolve, 0 broken.
`docs/DOCUMENTATION_INDEX.md` resolves 36/36 with 0 broken, so the
"refresh or retire" half needs no work either.
Original text:
**Priority:** P3

`docs/markdown/Scripts` has pre-existing broken image/file links, untouched
by the images_scripts_uml -> Scripts/assets move (all moved links verified
at the time):
- `wavedrom_troubleshooting.md` -> `assets/wavedrom/*.svg` — dir never
  existed here (18 references, still broken 2026-08-09)
- `cheat_sheet.md` -> `../rtl/_wavedrom_svg/*.svg` — dir gone
- `generate_uml.md` -> `../../puml_img/CocoTBFramework*.png` — UML renders
  gone; the tool lives in RDS-DV now, so the page may belong there entirely
- `md_to_docx.md` -> diagram.json examples — illustrative snippets; possibly
  fine as-is, mark as examples

Triage each: repoint, regenerate, or prune when the Scripts book gets its
pass (the docs-review area has "Scripts overview: write it" pending — do
these together). Related: `docs/DOCUMENTATION_INDEX.md` still catalogs the
pre-cleanup docs/ layout — refresh or retire it now that the handbook exists
(owner flagged 2026-07-22; its TESTING.md entry was repointed to the
handbook when /TESTING.md was retired 2026-08-09).

---

---

## TOOL-019: delta's lint runs, passes, and gates nothing

**Priority:** P3
**Status:** Closed 2026-09-23. delta is on `rtl/make/area.mk` like every other
area: a four-line `rtl/Makefile`, `filelists/delta_axis_flat_4x16.f` and the
`filelists/delta_all.f` master, plus an area entry in `bin/filelists.toml`.
Zero `|| true` remain, and it now ELABORATES: "PASS delta: Verilator lint
(1 modules, each as its own top)".
**The judgement this entry deferred, and the answer.** It asked whether a
single-module stub warrants a filelist and a registry area. It does. The repo's
own rule is that a module with no `.f` has no consumers and is
indistinguishable from dead code -- and the cost turned out to be trivial,
because `delta_axis_flat_4x16.sv` instantiates NOTHING and needs only
`reset_defs.svh`, which `area.mk` already supplies via `-I rtl/amba/includes`.
No `EXTRA_INCLUDES` override was needed. `rtl_test/` holds other shapes from
the same generator and is deliberately outside `rtl_roots`: generator output,
not this area's compile closure.
**Owner:** TBD

The last area still on the old per-file lint template. `make lint-delta`
exits 0 always, because the recipe lints each `.sv` individually and ends
every invocation with `|| true`:

    verilator --lint-only ... $file > lint_reports/... 2>&1 || true; \
    verible-verilog-lint ... $file > lint_reports/... 2>&1 || true; \

Three `|| true` remain in `projects/components/delta/rtl/Makefile`; every
other area has zero. It also never elaborates -- no `--top-module`, no
filelist -- so it would not catch what the same defect hid in misc
(axi4_slave_rom could not elaborate at its own defaults; see [[TOOL-017]]).

**Why it was left out of TOOL-017.** The fix applied everywhere else was a
four-line `rtl/make/area.mk` include plus `filelists/<area>_all.f`. delta has
**one** `.sv` (`delta_axis_flat_4x16.sv`), **zero** filelists, and no entry in
`bin/filelists.toml`, so converting it means inventing both a filelist and a
registry area for a single-module stub. That is a judgement call about an area
that may not warrant one, not a mechanical conversion, so it was filed rather
than guessed at.

delta is not in `COMPONENTS`, so `make -C projects/components lint-all` does
not cover it; only the top-level `lint-delta` / `lint-projects` do. Its shell
syntax error (empty `$(call print_*)`) WAS fixed under TOOL-017 -- it surfaced
the moment the masking `|| true` came off the top-level target -- so the target
runs today. It just does not gate.

<!-- Moved from vault/Tasks/amba/ 2026-09-14: the root cause is the pytest-xdist runner deleting local_sim_build concurrently, which hits every area, not amba RTL -->

---

## TOOL-005: env_python hardcodes /mnt/data/tools
**Priority:** P3
**Status:** Closed 2026-09-23. `env_python` now honours
`RTLDS_TOOLS_PREFIX` (default `/mnt/data/tools`), used for the oss-cad-suite
PATH, the sv2v PATH and the `VERILATOR_PIN=5.020` fallback.

**The block was also mis-nested, which this entry did not know.** The
oss-cad-suite test opened at line 75 and its export sat at line 80 -- AFTER a
complete inner `if/fi` for sv2v -- and the sv2v test was duplicated verbatim
either side of it. So the suite only reached PATH on a machine that also had
sv2v, and on a machine with neither, nothing was exported and nothing said so.
The two tests are flat and independent now.

Verified: `bash -n` clean; sourcing resolves verilator 5.045, yosys and sv2v
from the prefix; and `RTLDS_TOOLS_PREFIX=/tmp/nowhere source env_python` puts
no oss-cad-suite on PATH, so the override genuinely takes effect rather than
being shadowed by the default.

The 117-Makefile `SV2V` split found while doing this is filed separately as
TOOL-020 -- it is `formal/`, not `env_python`.
**Owner:** TBD

`env_python` works unmodified in a sandbox *provided* tools install to
`/mnt/data/tools`. If they land anywhere else, `install_tools.sh --prefix`
prints three `export PATH` lines the user must paste, and the ordering matters
(the pinned Verilator must be prepended LAST so it beats oss-cad-suite's 5.045).

That is a footgun: paste them in the wrong order and you silently simulate on
5.045, which is exactly what the pin exists to prevent.

Make `env_python` honour a `RTLDS_TOOLS_PREFIX` (defaulting to
`/mnt/data/tools`) so the prefix is set once and the ordering is not the user's
problem. See [[cloud-sandbox]].

---

---

## TOOL-002: Migrate the remaining method docs out of bin/ into the handbook
**Priority:** P2
**Status:** Closed 2026-09-23. Four of the seven reduced or retired; three kept
DELIBERATELY, which is the decision this entry asked for and did not make.

**Reduced to pointers** (the `bin/review/README.md` shape):
- `md_to_docx_install.md` 98 -> 12. Generic walkthrough -- install Python, make
  a venv, install Pandoc -- with nothing repo-specific in it.
- `md_to_docx_usage.md` 104 -> 13. **It was WRONG, not merely redundant.** It
  documented `-t/--template`, `-o/--output` and `--verbose`, none of which the
  tool has, and `md_to_docx.py input.md` with one positional when it takes two.
  Following it produced an argparse error. `--help` is now the pointer, because
  it is generated from the parser and cannot drift.
- `HEADER_TOOL_USAGE.md` 285 -> 9. 285 lines restating
  `add_file_headers.py --help`, which already carries the flags AND the
  dry-run / per-directory examples.

**Retired outright:** `markdown_to_word_instructions.md` (417 lines) documented
`markdown_to_word.py` -- a tool that has never existed in this repo. Not on
disk, not tracked, not in history, imported by nothing; its CLI (`--dir/--out`)
is not md_to_docx.py's. The entry says "do not delete outright", and that rule is
right for a doc whose tool exists; a redirect to a tool that was never here
points nowhere. It carried 24 broken links -- the single worst file in
DOCREV-011's tally -- because they pointed into that absent toolchain.

**KEPT as canonical mechanics, and this resolves the "known inconsistency":**
`DOC_GENERATION.md` (356), `SIGNAL_CONTRACTS_KMAPS.md` (118) and
`SIGNAL_NAMING_AUDIT.md` (451). The handbook deliberately points OUTWARD at the
first two -- `doc-pipeline.md:8` "Canonical how-to: bin/DOC_GENERATION.md. This
note carries the decisions and traps; the mechanics live there", and
`signal-contracts-and-kmaps.md:13` "Methodology (canonical):
bin/SIGNAL_CONTRACTS_KMAPS.md". That is a chosen split (rationale in the
handbook, mechanics beside the tool), not rot, and DOC_GENERATION.md carries 356
lines the handbook genuinely lacks: the 6-step stand-up, document-unit anatomy,
`<doc>_index.md` semantics, styles YAML, the generate script. Collapsing it would
change what `doc-pipeline.md` IS.

**What that leaves for Sean, deliberately not decided here:** CLAUDE.md's rule is
absolute ("no README beside a tool restating how to use it"), and the split above
is a documented exception to it. Either the rule gains a "tool mechanics may live
beside the tool, rationale in the handbook" clause, or those three move and the
two handbook notes stop deferring outward. Both are defensible; it is a
doc-architecture call, not a cleanup.

**RESOLVED 2026-09-25 (Sean): the rule gains the clause.** Tool mechanics may
live beside the tool, with the rationale in the handbook. The three files stay,
and `doc-pipeline.md` / `signal-contracts-and-kmaps.md` keep deferring outward
-- that split is now documented in root `CLAUDE.md` and [[doc-placement]] rule 1
rather than standing as a contradiction. The test that comes with it: mechanics
a reader of that directory needs may stay; method that applies everywhere goes
to the handbook. That same test now governs the subsystem `CLAUDE.md` files.
**Owner:** resolved.

The `- [ ]` checklist below is STALE and is kept only for history: the work it
lists was completed in this same entry above. `HEADER_TOOL_USAGE.md` is 9 lines,
`md_to_docx_install.md` 12 and `md_to_docx_usage.md` 13 -- all already reduced to
pointers; `markdown_to_word_instructions.md` was retired; and the remaining three
are the kept-by-exception cases. Nothing in it is outstanding.

`CLAUDE.md` now states the handbook is the single source of truth for skills and
methods, and that methodology does not live next to the code. Seven files in
`bin/` still do. They were deliberately left when the Kimi migration was scoped
to Kimi only — this is the follow-through, not new work.

- [ ] `bin/DOC_GENERATION.md` — the doc pipeline how-to
- [ ] `bin/HEADER_TOOL_USAGE.md`
- [ ] `bin/markdown_to_word_instructions.md`
- [ ] `bin/md_to_docx_install.md`
- [ ] `bin/md_to_docx_usage.md`
- [ ] `bin/SIGNAL_CONTRACTS_KMAPS.md`
- [ ] `bin/SIGNAL_NAMING_AUDIT.md`

Method content moves into the relevant handbook note (mostly
[[doc-pipeline]] and [[signal-contracts-and-kmaps]]); each file is reduced to a
short pointer, as `bin/review/README.md` already is. Do not delete outright —
someone landing in `bin/` should still be redirected.

**Known inconsistency to resolve as part of this:** `doc-pipeline.md` currently
calls `bin/DOC_GENERATION.md` the "canonical how-to", which contradicts the rule
one note away. Whichever way it resolves, the two must agree.

**Distinguish artifacts from documentation.** Files the code *reads* are not
documentation and stay put — `bin/review/REVIEWER_BRIEF.md` and
`docs/kimi_humanization_style_guide.md` are loaded verbatim as prompts. Check
before moving anything.

---

---

## TOOL-006: Triage the 18 Dependabot vulnerabilities on the default branch
**Priority:** P2
**Status:** Closed 2026-09-23 -- nothing to triage. The headline was stale.

Measured via `gh api /repos/sean-galloway/RTLDesignSherpa/dependabot/alerts
--paginate`: **74 alerts, all 74 in state `fixed`, zero open, zero by severity.**
All pip ecosystem, against `requirements.txt` (85 pins). Earliest fixed
2023-09-29, most recent 2026-09-16.

So the three checkboxes below have no subject: there is nothing to classify,
nothing safe-to-bump outstanding, and no accepted risk to record. The entry's own
closing note -- "check whether any are already fixed by the current pins before
doing work" -- was the right instinct and is the answer.

The push banner quoting "18 vulnerabilities (14 high, 4 moderate)" is what a
stale local view of an alert list looks like; the API is the authority.
**Owner:** TBD

Every push prints: *"GitHub found 18 vulnerabilities on
sean-galloway/RTLDesignSherpa's default branch (14 high, 4 moderate)."* It has
been printing that all session and is tracked nowhere, which is how a warning
becomes wallpaper.

- [ ] Read the Dependabot alerts and classify: real exposure vs transitive dev
      dependency that never runs on untrusted input.
- [ ] Bump what is safe to bump; `requirements.txt` is pinned, so each bump is
      a deliberate edit and needs a regression run behind it.
- [ ] Record anything deliberately not fixed, with the reason. An accepted risk
      that is written down is fine; an unread alert is not.

Note the alerts are against `main`, and the working branch has moved on — check
whether any are already fixed by the current pins before doing work.

---

---

## TOOL-020: `formal/` has two competing conventions for where sv2v lives
**Priority:** P3
**Status:** Closed 2026-09-23 (598b78d9b). Filed and closed the same day -- the
sweep turned out to be mechanical once measured, so holding it open would have
been the TOOL-017 defect again (an entry whose status disagrees with the tree).

All 117 harnesses now read `SV2V      ?= sv2v`. `?=` so an environment or
command-line override can pin a specific binary without editing 117 files;
PATH resolves the default, and env_python sets that from RTLDS_TOOLS_PREFIX
(TOOL-005).

**The first three verification attempts were worthless, which is the part worth
keeping.** I smoke-tested `formal/converters/uart_tx` -- it passed before and
after, and has no SV2V line at all: its recipe is `sby -f *.sby`, and sby drives
sv2v from the .sby file. I was testing a Makefile the sweep never touched, and
the override probes returned 0 hits for that same reason, not because `?=`
failed.

Redone against `formal/amba/apb4_master_stub`, which defines SV2V at line 12 and
expands `$(SV2V)` at line 34: default resolves to `sv2v`; command-line AND
bare-environment overrides both reach the recipe; a forced rebuild (removing the
generated `.v`) invokes sv2v exactly once and passes rc=0, SBY DONE (PASS); and
`SV2V=/nonexistent/sv2v` fails rc=2 with the bogus path in the recipe. So the
variable is load-bearing, not decorative.

Mechanically clean: +117 -117, every file exactly one line swapped, each left
with exactly one definition and its tab-indented recipes intact.
**Owner:** TBD

Found 2026-09-23 while closing TOOL-005, and deliberately NOT folded into it:
TOOL-005 is about `env_python`, and this is 117 formal harness Makefiles.

Three spellings across `formal/`:

    SV2V      := /mnt/data/tools/sv2v     85 files
    SV2V      := sv2v                     31 files
    SV2V := sv2v                           1 file

So a machine whose tools are not at `/mnt/data/tools` runs 31 harnesses and
fails 85, and nothing says which is intended. Nothing in the repo exports
`SV2V`, so the bare-`sv2v` form depends entirely on PATH -- which
`env_python` now sets from `RTLDS_TOOLS_PREFIX` (TOOL-005).

**Fix:** one form, `SV2V ?= sv2v`, letting PATH resolve it and an environment
override win. `?=` rather than `:=` so a caller can pin a specific binary
without editing 117 files. Do it as one mechanical sweep with a lint/formal
smoke run behind it, not file by file.

Not urgent: both forms work on THIS workstation today (the absolute path
exists and `sv2v` is on PATH), which is exactly why it has gone unnoticed.

---
