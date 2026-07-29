---
title: STREAM tasks
summary: Task rollup for the STREAM DMA component (projects/components/dmas/stream).
---

# STREAM tasks

Task tracking for the STREAM component (nested under `projects/components/dmas/`
to mirror the repo path). Lifecycle pages: [active](active.md) · [open](open.md)
· closed · dropped (created when first needed). Convention:
[Tasks](../../../../INDEX.md).

## Active (in progress)
- **TASK-056** — RFC Stage-E in-core R/W datapath perf monitors (retire
  `axi_bus_meter`): RTL + cosim complete; board bring-up pending.

## Open (not started)
- **TASK-058** (High) — Signal contracts + K-maps for the significant STREAM
  signals (especially the read/write engines) to prove the design correct by
  construction.
- **TASK-059** (High) — Fix the extended chained strided (transpose) descriptor
  corruption (silent data bug; repro is the `xfail`
  `test_stream_top_extended_chained_transpose`). See
  [known_issues/active/extended_chained_transpose.md](../../../../../../projects/components/dmas/stream/known_issues/active/extended_chained_transpose.md).

The component's old `TASKS.md` / `TODO_*.md` next to the code are being retired
into this area per the one rule (no task files beside code).
