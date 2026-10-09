---
title: Running regressions
summary: Always clean-all first; the Makefile targets, the levels, and how to read the result.
---

# Running regressions

**Always `make clean-all` first. Agents skip it and get lied to by stale build
directories.**

```bash
source env_python                       # non-negotiable: sets SIM=verilator, PATH, PYTHONPATH
cd val/amba                             # or val/common, val/math, projects/components
make clean-all && make run-all-full-parallel
```

Substitute the level you actually want: `run-all-{gate,func,full}-parallel`.
The same target names exist in `val/common/`, `val/amba/`, `val/math/`, and the
`projects/components/` master Makefile.

## Why clean-all is the load-bearing part

`clean-all` removes `local_sim_build/`, `sim_build/`, `logs/`, `__pycache__/`,
and VCDs. Every one of those is a place a stale artifact can survive an RTL or
testbench edit and make the run report something that is not true:

- Verilator reuses an existing `sim_build` dir. RTL edited, binary not rebuilt,
  test passes against the old design. **A green run that proves nothing.**
- `__pycache__` holds a compiled TB class whose source has since moved or been
  renamed - the import resolves to a file that no longer exists on disk.
- Old `logs/` make triage read stale failures as current ones, or hide that a
  test did not run at all this pass.

The failure mode is always the same shape: **the run gets more optimistic than
the code deserves.** A skipped `clean-all` does not usually produce a loud
error - it produces a pass you will trust and should not.

Skipping it saves a couple of minutes. Being wrong about whether the design
works costs hours, and costs them later, usually on the board.

## Running it is not the same as it working

`make clean-all` **aborts** when `REPO_ROOT` is unset:

```
Makefile:24: *** REPO_ROOT is not set. Please run: source $REPO_ROOT/env_python.  Stop.
```

It stops before deleting anything. So the habit of writing
`make clean-all >/dev/null 2>&1` — sending the noise to the bin and moving
on — hides the abort completely and leaves every artifact in place. The
subsequent run then reports against a stale build while its log claims the
tree was cleaned.

**`env_python` roots itself from wherever you are standing.** It sets
`REPO_ROOT` from `git rev-parse --show-toplevel` of the CURRENT directory,
not from its own location. Sourced from inside RDS-DV (say, after editing a
BFM there), it points `REPO_ROOT`, `PATH` and `PYTHONPATH` at the DV repo,
and a bridge test then dies with "File list not found:
/mnt/data/github/RTLDesignSherpa-DV/projects/components/fabric-gen-ip/bridge/rtl/filelists/..."
-- a path that names the wrong repository, which is the only clue. Measured
2026-09-10: four fresh tests failed at collection in 0.6 s with exactly that
message. `cd` into the main repo, source, then go where the tests are; and
when a run fails in under a second, read the path in the error before the
test name.

**Source `env_python` first, and check that the directories are actually
gone**, not that the command was typed:

```bash
source $REPO_ROOT/env_python
make clean-all
ls -d local_sim_build sim_build logs 2>/dev/null || echo "clean"
```

**Case study, 2026-08-16 (bridge BUG-002, was BRIDGE-003).** Six monitor stress tests were rerun
with `make clean-all >/dev/null 2>&1` in front of them and reported 6/6 in
7m22s. The clean had silently aborted; 18 GB and 88 build directories were
still on disk. Rerun after a *verified* clean, the same six took **35m50s** —
and still passed, so the conclusion survived. It did not have to. The tell was
the runtime: a suite that rebuilds from nothing cannot be five times faster
than the same suite the run before.

This is the [[silent-fallbacks]] pattern applied to your own tooling: the
step that was supposed to protect the result is itself capable of failing
quietly.

### Editing the RTL does not guarantee a rebuild, and the fiction points BOTH ways

`cocotb_test` decides whether to recompile by **content-hashing**, not by
timestamp. So re-running a test after editing the RTL can skip the compile and
measure the PREVIOUSLY built design. A `touch` does not help; only deleting the
build directory does.

This is worse than an ordinary stale-build false green, because the stale result
is not reliably optimistic -- it is just *wrong in whichever direction the old
binary happened to be*. The scoria session hit it mutation-testing FUBs
(2026-09-30): three mutations read as "caught by the targeted case, **missed** by
the random soak", which is a precise, plausible, actionable finding about soak
coverage. It was fiction. With `rm -rf fub/local_sim_build/test_<name>_*` before
each run, the soak caught all three. A plain false green at least fails in one
known direction; this invents a coverage gap that does not exist and sends you to
fix it.

So any loop that edits RTL and re-runs pytest -- mutation testing above all, since
its whole method is edit-then-measure -- needs an explicit build-directory delete
per iteration, not a clean-all at the start and not a `touch`.

**A second instance, with a different signature (reed-solomon, 2026-09-30).**
The edit was PYTHON only -- a testbench fix, no RTL touched, so no recompile
was even due -- and the run still came back "6 passed in 8.47s" where the same
six cells take 122s from clean. Deleting the build directory and re-running
gave the honest 122s and the same verdict. Two things to take from it: the
trap is not confined to RTL edits, and **duration is the only reliable tell**.
A result whose wall clock is an order of magnitude short of the known-clean
time has not run, whatever it says.

**Mutation testing is self-protecting in one direction, which is worth knowing
before you panic about past results.** A stale build means the mutation was
never compiled, so the test behaves as if unmutated and PASSES -- and a
mutation check reads a pass as "this assertion has no teeth". The failure mode
is therefore a false NEGATIVE: it makes you distrust an assertion that is
actually sound. A mutation that DOES fail the test proves the mutated RTL was
compiled, so every positive detection is trustworthy without re-running. The
reed-solomon session re-verified its most consequential check both ways with
explicit build deletes -- unmutated 20.6s pass, mutated 19.6s fail, both real
durations -- and the conclusion held. What you cannot trust on a possibly-stale
build is a mutation that came back CAUGHT-BY-NOTHING.

One qualification on "every positive detection is trustworthy": it holds when
the mutation and the assertion are the only moving parts. A mutation that fails
for a DIFFERENT reason than the one planted proves something was loaded, not
that your assertion is the thing with teeth. The tell is a failure message
naming an unrelated check, so **read which assertion fired, not just that one
did** -- cheap, and the only gap in the argument above.

**The tell is the same one as everywhere else in this note: duration.** A full
case set that takes 70s from clean came back in 0.4s. Before believing any
mutation verdict, check that the run was long enough to have compiled anything.

### Restoring the source is not enough: purge the caches too

A third instance, and the one with no build step at all (RLB-cleanup,
2026-10-01). Mutating `board.py` from `serial in t["serial"]` to
`serial == t["serial"]`, running pytest, then restoring the file with `cp` left
the suite **still reporting the mutated result**. `git diff` was clean and the
restored source was correct on disk; the run was reading
`__pycache__/board.cpython-312-pytest-9.1.1.pyc`, pytest's assertion-rewritten
bytecode.

Two things make this one nastier than a stale sim build:

- **The mutation was the same byte count.** `in` and `==` are both two
  characters, so any cache validation that leans on source size sees no change.
- **There is no duration tell.** These are sub-second unit tests either way, so
  the heuristic that catches the cocotb cases above is useless here.

It was caught only because the restored run disagreed with a run of the same
code minutes earlier, and the contradiction was chased instead of explained
away. The false reading was in the *flattering* direction too -- it credited a
fixture change with catching a regression that its own cache had manufactured.

**So a mutation loop restores the source AND removes `__pycache__` and
`.pytest_cache` on every iteration**, not once at the start. The same applies to
reverting after any experiment: `git diff` reporting clean says the SOURCE is
restored, not that the next run will execute it.

### The two stale-artifact failures point in OPPOSITE directions

Which artifact is stale decides which way the lie runs, and the two are not
equally dangerous.

| Stale artifact | Mutation appears to | Reads as | Sends you to |
| --- | --- | --- | --- |
| Python bytecode (`__pycache__`) | **fail** | the check has teeth | trust a guard you have not tested |
| Sim build (`sim_build/`, `local_sim_build/`) | **pass** | the check is vacuous | rewrite a test that was fine |

The bytecode case manufactures a catch; the sim-build case manufactures a hole.
The second is the safer failure -- it costs an afternoon rather than shipping a
false assurance -- but both are avoidable by the same purge.

### Content-match the failure to the mutation

The strongest tell, and it works in both directions where a pass/fail check
cannot: **read WHICH assertion fired and confirm the text corresponds to the
mutation you planted.** Two sessions arrived at this independently on the same
day (rapids and reed-solomon, 2026-10-01).

- A real detection names the thing you broke. Forcing `w_drop_rpt` to 0 produced
  "monitor reported 0 dropped event(s)" -- a string that exists only in the
  post-fix testbench, so no cache could have produced it.
- A mutation that fires a DIFFERENT assertion proves something ran, not that the
  check under test has teeth. One mutation broke data so comprehensively (44 of
  47 checks) that the data scoreboard fired and the timing assertion being
  validated was never reached; another was absorbed by a downstream skid buffer,
  so the DUT did not change at the point being measured. Both "failed". Neither
  was evidence.

So a mutation is only evidence when it perturbs the thing you are validating,
and nothing upstream of it, and the failure text says so.

## The aggregator's area list is a claim, not a measurement

`bin/aggregate_test_results.py` runs what `test_environments.toml` names in
`sub_areas`, and prints PASS over the total. The total is only the areas it was
told about. rapids' list read `["fub", "fub_beats", "macro", "macro_beats"]`
from 2026-03-31; `top_beats` was created on 2026-07-17 (a1760aaf6) and never
added. So on 2026-09-26 "RAPIDS FULL 579/579 PASS" was true and useless: the
ten top-level cells were not in it, and one of them
(`test_rapids_beats_top_perf_window`) was red at HEAD because the monitor-lite
swap had removed the descriptor monitor's perf window. A peer session running
the area Makefile directly (`AREAS="macro macro_beats top_beats"`) found it in
one pass.

Two habits, one guard:

- **Name the areas in the claim.** "RAPIDS FULL green" is not a result;
  "rapids fub 15, fub_beats 303, macro 12, macro_beats 249, top_beats 10" is.
  If you cannot list them you do not know what ran. The same rule already
  applies to repositories ([[feedback_ci_green_name_the_repo]]).
- **Count the directories, not the list.** Before trusting a component
  total, `ls -d <component>/dv/tests/*/` and compare with `sub_areas`. The
  component Makefile's own `AREAS ?=` default is the second source of truth
  and was correct here; the aggregator's copy was the stale one.
- The aggregator now prints `WARNING: <env>: <dir> has a Makefile and
  test_*.py but is not in sub_areas` for every directory the list misses. A
  warning on stderr is a weak gate; the fix is to add the area, which is what
  the warning tells you to do.

## Levels

| Level | Env | Scope | Use |
|---|---|---|---|
| GATE | `REG_LEVEL=GATE` | ~30 s/module, 2-5 ops | pre-commit, after a small change |
| FUNC | `REG_LEVEL=FUNC` (default) | ~2-3 min/module, 10-30 ops | normal development, CI |
| FULL | `REG_LEVEL=FULL` | ~10-30 min/module, 100+ ops | pre-release, board gate, sign-off |

Integration tests in `projects/components/` use `TEST_LEVEL=gate|func|full`
instead. See [[tb-structure]].

Raw `pytest` on a directory does **not** give you a regression - it gives you
whatever the default level is (FUNC), with no clean, no `-n` parallelism, and
no reruns. The Makefile targets add `-n`, rerun-on-failure, and the level. Use
the target; do not hand-roll the pytest line.

## Some areas have a gate the module suite cannot be

A component's own `dv/tests` suite can be green and still not have gated the
thing that ships. pumice is the worked example: `ddr2_char_framework/dv/tests`
is the only suite that builds the board's x16 / strict-timing configuration, and
an arbiter fix once passed all 213 pumice fub/macro/top tests while failing 7
there. **The char-framework sim is the board gate, and it runs before any
pumice RTL commit.**

The failure mode is quieter than a red suite: that area had silently stopped
gating because the Makefile's `run-all-*` targets were being swallowed by a
`run-%` pattern into a nonexistent test id, so the gate invocation exited clean
having run nothing. Aliases fixed it 2026-09-08. A gate that runs nothing looks
exactly like a gate that passes.

Two rules follow, and they generalise beyond pumice:

- **If an area has a configuration only one suite builds, that suite is the
  gate** — regardless of which directory the edit was in.
- **A gate's verdict is its EXIT CODE**, plus whatever success line the runner
  prints. Not the pass counts. On 2026-09-25 a pumice gate exited `rc=2` with 8
  FAILED lines and was reported as green, because the check grepped for
  `passed` and took the last three lines: three real green summaries from
  earlier groups. The commit shipped with two unit tests broken. Both signals
  that would have caught it — the exit code, and the runner's
  `OK: ... passed at BOTH geometries` line — were absent and neither was
  checked.

(Was `vault/Tasks/pumice-ddr2-lpddr2/task/dropped/TASK-003.md`, which was a rule filed as a
task and therefore could never be closed.)

## Serial ordering that matters

At the `projects/components/` level, `make run-all-full-parallel` is serial per
component and serial `fub -> macro -> top` within a component, parallel only
inside a stage. That ordering is deliberate: a macro failure is much cheaper to
read when you already know the fubs underneath it are green. Do not "optimize"
it into a flat parallel sweep.

## Reading the result

`rc=0` and an explicit pass count. Do not report a regression as clean from
`rc` alone - quote the counts (`156 passed`, `533 passed`). If the count is
lower than last time, tests did not run; that is a failure even when nothing
is red.

## A shared worktree makes "clean" a claim you have to check

Two things bite here, and both are silent.

**Cleanup can delete a run that is still going.** `clean-build` used to be
`rm -rf` plus a recursive `find ... -exec rm -rf {} +` across the subtree, and
`fpga_flow.mk` had no sim-build target at all, so anyone wanting a cold cosim
typed the `rm -rf` by hand. Either way a concurrent session's in-flight build
disappears, and the failure does not look like a deletion -- it surfaces as a
missing file inside Verilator, or a model that finishes and is simply wrong.
`vault/Tasks/amba/open.md` records three occurrences before the cause was
found. Both targets now call `bin/clean_sim_builds.py`, which reads the
`.sim_busy` marker `sim_build_path()` writes and skips directories whose owning
pid is still alive, reporting what it skipped. Liveness is the test, not
session identity: everyone who has not set `SIM_BUILD_ROOT` is `session=shared`,
so an "is it mine?" check compares 'shared' to 'shared' and cleans straight
through a live build.

**The framework can move underneath a long run.** cocotb re-imports per test,
so a mid-run edit to `CocoTBFramework` means early and late cases ran different
code -- and the run still reports one number. Fingerprint it:

    find <site-packages>/CocoTBFramework -name '*.py' | sort | xargs md5sum | md5sum

before and after. It costs seconds. Measured 2026-08-28: two consecutive
68-minute `build-perf` runs were BOTH caught this way, the second after
deliberately waiting for the tree to settle. Without the check the second would
have been reported as clean, with more confidence than the first.

When the hashes differ, do not simply re-run -- a third attempt in a shared
worktree is as likely to be dirty as the first two. Ask instead what actually
moved and whether the suite touches it. Both those runs scored 36/36 under
different `gaxi_slave` states, and nothing under `val/` or `bin/TBClasses/`
passes `ready_policy`, so the churn was provably inert. Two agreeing runs
under different framework states is stronger evidence than one pristine run,
and it is evidence you can actually obtain.

**RTL can move underneath a long run too, and it looks like your failure.**
Measured 2026-09-10 on the bridge: a FULL run reported 8 failed / 229 passed
across four distinct tests, three of them the boundary probes that had just
been changed, which is exactly where a new finding would surface. None of it
was the bridge. Every one of the eight was Verilator exiting non-zero, and all
eight named the same shared source, `rtl/common/fifo_control.sv`, which another
agent had caught half-written mid-conversion to the reset macro: the compiler
died on an unterminated macro argument list at end of file. The file linted
clean an hour later and the identical suite ran 237/237.

The tell is the ERROR KIND, and it is one grep:

    grep -oE "^E   [A-Za-z_.]*(Error|Exception|SystemExit)" <log> | sort | uniq -c

A build exit is never a test result. Assertions carry the test's own message
and name the DUT; `SystemExit: Process perl terminated with error 1` names
nothing, because nothing ran. Read the kind before the test name -- the test
name is the most misleading thing in the log, since it points at whatever you
touched most recently rather than at what broke. Then find the real error with
`grep -iE "%Error|cannot|No space|Killed"` and check whether the file it names
is even yours.

The same reasoning covers load. A run of the same suite that reports reruns
when the previous identical run reported none has a scheduling explanation
available before it has a code explanation; check the load average the run
executed under before believing a timeout.

Related: [[seeds-and-determinism]] (a rerun that changes seeds is not a
reproduction), [[bfm-usage]], [[coverage]].

## A cocotb version bump runs TWO matrices, and the second one is the trap

Measured 2026-10-08 (tooling BUG-015). The 2.1.0 flip matrix gated TASK-025
on the `val/` BKM areas — math, common, cdc, bridge — and was pronounced
green on pass counts. The same flip broke every silicon/sim-equivalence UART
suite at startup: sixteen files still imported `cocotb.external` /
`cocotb.function`, which 2.x removed, and not one of those suites was in the
matrix. Every one of them failed at time 0 with
`module 'cocotb' has no attribute 'function'`. The breakage surfaced by
accident a day later, through a board-matrix `verify-sim` gate that happened
to exist for an unrelated reason.

The `val/` matrix cannot catch this class: the UART suites are the only
consumers of the bridge-to-host threading API (`cocotb._bridge` today —
`bridge`/`resume`; the harness shim is `bin/TBClasses/harness/cocotb_axil_bridge.py`),
so an API removal kills them and only them, at import time, before a single
test body executes. A suite that dies at startup does not fail the areas you
ran; it is absent from them.

Rule: a cocotb minor or major bump does not move the pin until BOTH halves
ran clean from `clean-all`:

1. the `val/` BKM matrix — `make clean-all && make run-all-full-parallel`
   per area (math, common, cdc, bridge);
2. every `cocotb._bridge` consumer suite, at FUNC from clean. Derive the
   list from the tree on the day you run it — do not recall it:

       grep -rl "cocotb\._bridge" bin/TBClasses projects --include='*.py'

   As of BUG-015 the consumer suites are (one command each, all
   `source env_python` first):

   | Suite | Command |
   | --- | --- |
   | RS loop UART | `make -C projects/fpga-systems/Genesys2/ecc-ip/reed-solomon/build-loop clean-all sim` |
   | BCH loop UART | `make -C projects/fpga-systems/Genesys2/ecc-ip/bch/build-loop clean-all sim` |
   | stream build-mon | `make -C projects/fpga-systems/Genesys2/dma-ip/stream/build-mon clean-all sim` |
   | rapids byte harness | `make -C projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids clean-all sim` |
   | rapids char harness | `make -C projects/fpga-systems/Genesys2/dma-ip/rapids_beats/flows-rapids-beats clean-all sim` |
   | pumice ddr2 char | `make -C projects/fpga-systems/NexysA7/mem-ctrl-ip/pumice/ddr2_char_framework/dv/tests clean run-func-parallel` |
   | cdc demo UART | `make -C projects/fpga-systems/NexysA7/misc-ip/cdc_counter_display/build-demo <sim target>` |

   If the grep finds a directory not in the table, that IS the finding: add
   its suite before flipping.

Quote pass counts for both halves, the same as any other regression. The
2026-10-09 re-run of the five non-routine suites under 2.1.0 is the worked
example recorded in tooling BUG-015.
