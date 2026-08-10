---
title: FPGA notes
summary: Board process - common infra, then board/component specifics.
---

# FPGA

## Common infrastructure

Board-agnostic method and shared code -- the canonical patterns every flow
reuses -- live in one place:

- [cmn-infra/](cmn-infra/INDEX.md) - [[uart-harness]], the [[host-stack]] py
  plumbing, [[build-flows]], [[timing-closure]], [[timing-triage-tool]], [[boards]]

Start with [[area-structure]] if you are adding a board, a component or a build;
[[flow-migration]] if you are moving an existing flow into that layout.

## Boards / components

Board- and component-specific FPGA docs nest by target (the layout the repo
Linux paths will grow into) - they are NOT flat handbook notes:

- [NexysA7/stream-char/](NexysA7/stream-char/INDEX.md) - STREAM characterization (bridge) flow + the [[host-tools]] runner suite
- [Genesys2/stream/](Genesys2/stream/INDEX.md) - **the STREAM component in the
  new layout**: build-mon (migrated, board-verified) + build-perf (pending)
- [Genesys2/stream-mon/](Genesys2/stream-mon/INDEX.md) - the monitor coverage
  design + campaign notes, still written against the pre-migration paths
