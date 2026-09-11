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
/mnt/data/github/RTLDesignSherpa-DV/projects/components/bridge/rtl/filelists/..."
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

**Case study, 2026-08-16 (BRIDGE-003).** Six monitor stress tests were rerun
with `make clean-all >/dev/null 2>&1` in front of them and reported 6/6 in
7m22s. The clean had silently aborted; 18 GB and 88 build directories were
still on disk. Rerun after a *verified* clean, the same six took **35m50s** —
and still passed, so the conclusion survived. It did not have to. The tell was
the runtime: a suite that rebuilds from nothing cannot be five times faster
than the same suite the run before.

This is the [[silent-fallbacks]] pattern applied to your own tooling: the
step that was supposed to protect the result is itself capable of failing
quietly.

## Levels

| Level | Env | Scope | Use |
|---|---|---|---|
| GATE | `REG_LEVEL=GATE` | ~30 s/module, 2-5 ops | pre-commit, after a small change |
| FUNC | `REG_LEVEL=FUNC` (default) | ~2-3 min/module, 10-30 ops | normal development, CI |
| FULL | `REG_LEVEL=FULL` | ~10-30 min/module, 100+ ops | pre-release, board gate, sign-off |

Integration tests in `projects/components/` use `TEST_LEVEL=basic|medium|full`
instead. See [[tb-structure]].

Raw `pytest` on a directory does **not** give you a regression - it gives you
whatever the default level is (FUNC), with no clean, no `-n` parallelism, and
no reruns. The Makefile targets add `-n`, rerun-on-failure, and the level. Use
the target; do not hand-roll the pytest line.

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
