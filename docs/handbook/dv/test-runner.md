---
title: Test runner
summary: The Makefile -> pytest -> cocotb_test.run -> Verilator stack; REG_LEVEL vs TEST_LEVEL, unique build dirs, artifact layout.
---

# Test runner structure

Four layers, each with one job. Knowing which layer owns a behaviour is what
makes a failure quick to place.

| Layer | Owns | Where |
|---|---|---|
| Makefile | level, `-n` workers, reruns, clean | `val/*/Makefile`, `projects/**/dv/tests/*/Makefile` |
| pytest wrapper | the parameter matrix, the build dir, env | `test_<module>.py` |
| `cocotb_test.run()` | elaborate + launch the simulator | framework |
| cocotb test fn | the actual stimulus and checks | same file or `cocotb_*.py` |

[[running-regressions]] covers which target to invoke. [[tb-structure]] covers
how to write the layers below `run()`. This note is the machinery between them.

The stack is deliberately the **same shape in every area** - `val/common`,
`val/amba`, and `projects/components/**` (STREAM is the reference project
implementation). A new test area should be recognisable as a copy of an
existing one; if it is not, that is the defect. The knobs are identical:

    PYTEST_XDIST  = -n 48
    PYTEST_RERUNS = --reruns 3 --reruns-delay 1
    clean-all     -> logs, local_sim_build, sim_build, __pycache__, VCD/FST, results XML

Only three sanctioned variations exist, each for a stated reason:

| Area | Variation | Why |
|---|---|---|
| `val/amba` | `--dist=loadgroup` on xdist | keeps tests sharing `@pytest.mark.xdist_group(name=)` on one worker, so producer/consumer pairs cannot race. Unmarked tests distribute as usual. |
| `projects/**` (STREAM) | `testcase="cocotb_test_*"` in `run()` | Pattern B: one pytest wrapper selects one cocotb function ([[tb-structure]]) |
| `projects/**` (STREAM) | worker id appended to the build-dir name | see below |

`clean-all` is composed differently in the project areas (`clean-all: clean`
plus an explicit `rm -rf logs local_sim_build sim_build`) but removes the same
set. Do not read the shorter target as a weaker clean.

## REG_LEVEL and TEST_LEVEL are different knobs

They are constantly confused because both take a level name.

- **`REG_LEVEL`** (`GATE|FUNC|FULL`, default FUNC) is read by the wrapper's
  parameter generator and decides **how many parameter combinations exist**.
  For `counter_bin`: GATE 2, FUNC 9, FULL 27.
- **`test_level`** is one axis *inside* those combinations, and is handed to the
  cocotb test as **`TEST_LEVEL`** in `extra_env`. It decides **how deep a single
  test runs** - operation counts, timing profile.

So `REG_LEVEL` selects the matrix; `TEST_LEVEL` sets the depth of each cell.
GATE typically emits only `test_levels = ['gate']` to keep the smoke pass fast,
while FULL sweeps `['gate', 'func', 'full']` across every parameter.

Setting `TEST_LEVEL` by hand on a Makefile target does **not** shrink the
matrix - you get the full parameter sweep at whatever depth you named, which is
usually not what was intended.

Timeouts scale off the same axis: `base_timeout * multiplier[test_level] *
max_factor`. A test that times out only at FULL is usually a missing multiplier,
not a hang.

## One build directory per parameter set

The wrapper composes a human-readable identifier and derives everything from it:

    test_name_plus_params = f"test_counter_bin_w{width}_max{max_val}_{test_level}_{reg_level}"
    sim_build   = tests_dir/local_sim_build/<test_name_plus_params>/
    log_path    = logs/<test_name_plus_params>.log
    results     = logs/results_<test_name_plus_params>.xml

**This uniqueness is what makes `-n 48` safe.** Verilator build directories are
not concurrency-safe; two workers sharing one `sim_build` corrupt each other's
objects. Every parameter combination getting its own directory is the entire
mechanism, which is why the identifier must include every parameter that
changes the elaboration. Drop a parameter from the name and parallel runs start
failing in ways that look like RTL bugs.

Two strategies are in use, and the difference is deliberate:

- **`val/*`** encodes every axis in the name, including `test_level` and
  `REG_LEVEL`. The build dir is therefore stable across runs, so an unchanged
  parameter set reuses its build.
- **`projects/**` (STREAM)** encodes the parameters and then appends
  `PYTEST_XDIST_WORKER` when set. That guarantees isolation even if two
  distinct parameter sets happen to encode to the same string - cheap
  insurance where the identifier is built from formatted numeric fields that
  can collide. The cost is that the build dir changes with the worker, so
  builds are not reused between runs.

Prefer the STREAM form for new project areas. Collisions in a formatted
identifier are silent and present as flaky parallel failures.

It is also why `clean-all` matters so much - see [[running-regressions]]. A
stale `local_sim_build/<name>/` is reused silently.

## Path and source resolution

- `get_paths({tag: relpath})` returns `(module, repo_root, tests_dir, log_dir,
  paths)`. It infers the caller's directory from the **stack frame**, so it must
  be called from the test file itself, not from a helper - a wrapper function
  around it silently resolves paths relative to the wrapper.
  `repo_root` comes from `git rev-parse`, so tests need a git working tree.
- `module` is the calling file's basename and is what gets passed to `run()` as
  the Python module holding the cocotb tests.
- Sources come from `get_sources_from_filelist(repo_root, filelist_path)` -
  never a hand-listed array. Every component owns its own compile closure and
  consumers `-f` include it; see [[naming-and-style]]. Watch the `//` trap: it
  is a comment, so a doubled slash silently drops a source.
- Pattern B wrappers additionally pass `testcase="cocotb_test_<name>"` to select
  one cocotb function; see [[tb-structure]].

## Artifacts

    <tests_dir>/local_sim_build/<test_name_plus_params>/   Verilator build, dump.fst
    <tests_dir>/logs/<test_name_plus_params>.log           run log
    <tests_dir>/logs/results_<...>.xml                     junit XML

Waves are opt-in: `WAVES=1` sets `TRACE_FILE`/`COCOTB_TRACE_FILE` to
`dump.fst` in the build dir. `create_view_cmd()` writes a ready-made viewer
command next to the log so you do not have to reconstruct the path.

## Aggregating across areas

`test_environments.toml` at the repo root is the single source of truth for
which areas exist. `bin/aggregate_test_results.py --run` walks it, invokes each
area **through its own Makefile** - preserving that area's cwd, conftest and
environment - injects `--junitxml` via `PYTEST_ADDOPTS`, and renders the
collected results.

Running the areas by hand from one directory instead is the recurring mistake:
conftest and relative filelist paths are per-area, so the run either fails to
collect or quietly tests the wrong sources.

Related: [[seeds-and-determinism]], [[coverage]], [[cloud-sandbox]].
