# Bisecting a simulation regression

`git bisect run` against a cocotb suite is a trap-rich exercise, because every
way the harness can fail looks to git like a verdict about the design. Five
bugs, all from one hunt (pumice `concurrent_rw[bl4x16]`, 2026-09-22), each of
which produced confident output rather than an error.

## The exit-code contract is the whole game

    0    good  -- it SIMULATED and passed
    1    bad   -- it SIMULATED and failed
    125  skip  -- this revision could not be JUDGED

`git bisect run` treats every non-zero exit except 125 as BAD. A collection
error exits 2. An import error exits 2. A missing parametrization "fails". So
a harness that cannot run on a revision marks it bad, bisect converges on
nonsense, and nothing in the output says so.

**Everything that is not a verdict must map to 125.** Not just the obvious
`ERROR collecting` -- also `ModuleNotFoundError`, `ImportError`,
`INTERNALERROR`, `no tests ran`, and "the run was too fast to have simulated".
If the script cannot tell "this design is broken" from "this run never
started", the bisect is measuring the harness.

## Pin the harness; bisect only the design

A test's parametrization changes over time. Bisect the test along with the
design and the node id stops naming the same cell -- pytest exits fast and
every revision looks bad. Check the test (and its tbclasses/tb) out from the
known-bad tip **inside the run script, after bisect's checkout, on every
invocation**, because bisect's own checkout reverts a tracked file pinned
beforehand. Restore it before returning (`trap cleanup EXIT`) or the next
checkout fails on local modifications.

## A worktree needs its OWN env

Sourcing the main checkout's `env_python` while testing a worktree points
`PYTHONPATH` at one tree and the code under test at another. The symptom is
remote from the cause:

    from file_list_processor import FileListProcessor
    E   ModuleNotFoundError: No module named 'file_list_processor'
    /mnt/data/github/RTLDesignSherpa/bin/TBClasses/shared/filelist_utils.py:83

-- note the path is the MAIN repo while the worktree is under test. Source the
worktree's own `env_python` so every path is self-consistent.

## A pass and a failure have different runtimes -- do not floor on the failure

The anti-vacuity floor is right in principle ([[stale-sim-build-false-green]])
and lethal if calibrated on the wrong side. Here the FAILURE took 347s because
it waits out a 1,000,000-cycle timeout, while a PASS finished in 41s as soon as
the last beat landed. A 60s floor reasoned from the failure skipped every
legitimate pass and the bisect learned nothing across two runs. Calibrate the
floor against the FAST outcome, and keep it well above the collection-death
time (0.16s here).

## Never share a sim_build between concurrent runs

A bisect step that does `rm -rf <shared>/local_sim_build` will delete a build a
parallel run is using. It does not fail like a deletion -- it surfaces as a
corrupt model inside Verilator. `make/tests.mk` cleans through a marker-aware
script for exactly this reason. Give each step a private build root.

## Sanity check before trusting a result

Run the script by hand on one known-bad revision first and confirm it returns
a REAL duration and a REAL verdict. Two of the five bugs above survived
because the bisect "completed" and produced a plausible-looking answer.

Related: [[stale-sim-build-false-green]], [[running-regressions]],
[[measure-over-the-window]].
