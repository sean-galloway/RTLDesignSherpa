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

Related: [[seeds-and-determinism]] (a rerun that changes seeds is not a
reproduction), [[bfm-usage]], [[coverage]].
