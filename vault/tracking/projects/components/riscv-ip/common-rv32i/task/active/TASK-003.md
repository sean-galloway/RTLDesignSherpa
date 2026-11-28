# TASK-003: the core_drills app -- design doc, then the merlin modes and peregrine's predictor drill

**Priority:** P4
**Status:** active (filed 2026-11-25 deferred; design doc accepted 2026-11-28, all decisions as recommended, build started)
**Owner:** riscv-ip session (split out of riscv-ip/peregrine-rv32im TASK-003)

## Why

The falcon suite spec (`docs/superpowers/specs/2026-10-06-riscv-falcon-suite-design.md`,
"Suite-wide packaging" and build-order milestone 3) plans one drill app for
the whole core ladder, `bin/apps/core_drills`. It does not exist yet.
peregrine TASK-003 asked for its predictor drill (mode 3), which cannot be
built before the app; the owner split the app out and deferred it.

## What

In the spec's order:
1. A design doc for the app, before any code (spec: "The app gets its own
   design doc before implementation"). It follows the `bin/apps/ddr_drills`
   architecture: packs, a pure model layer, a node test suite, a
   cache-busted deploy, and a `bin/apps/launcher` entry.
2. Mode 1: the merlin pipeline stage viewer with forwarding arrows.
3. Mode 2: the merlin hazard quiz.
4. Mode 3: peregrine's branch-predictor drill. Its model must agree with
   the predictor model the peregrine TB uses
   (`peregrine-rv32im/dv/tbclasses/peregrine/bpred_model.py`): BTB 32,
   BHT 256, install at 01.

Modes 4 and 5 (the gyrfalcon ROB viewer, the garuda FP scheduler) arrive
with those rungs and are not part of this task.

## Done when

- The design doc is reviewed and accepted by the owner.
- Modes 1-3 pass the app's node test suite, and mode 3's outcomes match
  `bpred_model.py` on the peregrine predictor stress streams.

## Progress

- 2026-11-28: design doc `docs/superpowers/specs/2026-11-27-core-drills-app-design.md` accepted; D1-D8 all as recommended. Build started.
