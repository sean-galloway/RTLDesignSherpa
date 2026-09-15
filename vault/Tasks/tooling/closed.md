<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# Tooling tasks — closed (complete)

_None._

---

## TOOL-009: Python version mismatch breaks EVERY Verilator build on this box
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

## TOOL-017: `lint-<component>` is advertised but cannot run for two areas
**Priority:** P3
**Status:** 🔴 Not Started
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
