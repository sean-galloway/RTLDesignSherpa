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

## Boards / components

Board- and component-specific FPGA docs nest by target (the layout the repo
Linux paths will grow into) - they are NOT flat handbook notes:

- [NexysA7/stream-char/](NexysA7/stream-char/INDEX.md) - STREAM characterization (bridge) flow + the [[host-tools]] runner suite
- [Genesys2/stream-mon/](Genesys2/stream-mon/INDEX.md) - STREAM monitor coverage build + campaign
