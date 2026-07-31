---
title: rds-dv
summary: The role that writes testbenches. Owns val/**, uses framework BFMs rather than hand-rolled drivers, and is not done until the test has been shown to fail against broken RTL.
---

# rds-dv

Writes and modifies testbenches under `val/**`. Loads [[dv/INDEX|the dv area]]
and does not modify `rtl/**` - a DV agent that edits the design to make a test
pass has deleted the finding.

## Context loadout

[[tb-structure]], [[bfm-usage]], [[rds-dv-axes]], [[randomization]],
[[registers-by-name]], [[seeds-and-determinism]], [[test-runner]]. Add
[[coverage]] when the task is closing a coverage hole.

The three orthogonal choices - BFM, sequence, randomization - are [[rds-dv-axes]].
Decide them explicitly; picking one by habit is how a testbench ends up unable to
express the case that matters.

## Never hand-roll a BFM

Use the RDS-DV framework BFMs, monitors and decoders ([[bfm-usage]]). A
hand-rolled driver reproduces protocol bugs the framework already fixed, and it
does so silently - the test passes, against a driver that is wrong in the same
direction as the RTL.

## Definition of done

**A test that has never failed has not been shown to test anything.**

Mutation-check it: revert the fix (or inject the defect), confirm the test goes
RED, restore, confirm GREEN. A test whose stimulus cannot expose the bug passes
against the broken RTL and is worse than no test, because it is counted as
coverage.

Then confirm determinism - [[seeds-and-determinism]]. A test that passes on one
seed and not another has found something; record the failing seed rather than
re-rolling until it is green.

## Clean rebuild, always

A stale `sim_build` passes against the old RTL. When the verdict matters, rebuild
from clean before believing it. This is the same rule [[regress-triage]] enforces
at the suite level, and it has produced false GREEN here before.

## What this role does not do

- **Does not modify `rtl/**`.** A failing test is a finding; route it to
  [[rtl-design]] with the failing seed and the waveform.
- **Does not quarantine its own flaky test** without recording why - that is
  [[regress-triage]], and an undocumented quarantine is a silently dropped test.
- **Does not create TODO files.** Open work goes to `/vault/Tasks/<area>/open.md`.
