---
title: STREAM tasks
summary: Task rollup for the STREAM DMA component (projects/components/dmas/stream).
---

# STREAM tasks

**Next ID: TASK-083** — never recycle a number, even when its task closed.

Task numbers are scoped to THIS area. The same number exists in other areas and that is expected, not a collision -- amba's TASK-080 and this one are different tasks, and the area is what tells them apart. Cite one as "STREAM TASK-080" when writing outside this file.

Task tracking for the STREAM component (nested under `projects/components/dmas/`
to mirror the repo path). Lifecycle pages: [active](active.md) · [open](open.md)
· [closed](closed.md) · dropped (created when first needed). Convention:
[Tasks](../../../../INDEX.md).

## Active (in progress)
- **TASK-056** — RFC Stage-E in-core R/W datapath perf monitors (retire
  `axi_bus_meter`): RTL + cosim complete; board bring-up pending.

## Open (not started)
- **TASK-080** (Medium) — STREAM formal proofs read a hand-copied
  `gaxi_fifo_sync` (and an orphan package stub), not the RTL; convert
  them to flatten the real module with sv2v, as done for repo-root formal.

## Closed (done)

- **TASK-073** (Medium) — build-mon host walked `slvmon_apb` with the wrong
  regmap. Host half was already fixed; the superseded `slvmon_regs` set is
  now deleted. Done 2026-09-20.

- **TASK-058** (High) — Signal contracts + K-maps for the significant
  STREAM signals. Done 2026-09-20; optional formal SVA not done.

- **TASK-060** (High) — Kick STREAM from its own registers. Done 2026-09-18.
- **TASK-081** (Medium) — `test_stream_top_basic` omitted `channel_id` when writing
  descriptors, filing every channel's under `ch0`; the engine-vs-descriptor
  scoreboard then compared two channels' descriptors against one channel's beats.
  A TEST defect, latent since the scoreboard landed, surfaced when [[TOOL-016]]
  unpinned the generator and multi-channel cells were emitted for the first time.
- **TASK-059** (High) — Fixed the extended chained strided (transpose) descriptor
  corruption: gated the run-base generator start on `w_is_ext` in `scheduler.sv`.
  Repro `test_stream_top_extended_chained_transpose` now passes. See
  [known_issues/resolved/extended_chained_transpose.md](../../../../../../projects/components/dmas/stream/known_issues/resolved/extended_chained_transpose.md).

The component's old `TASKS.md` / `TODO_*.md` next to the code are being retired
into this area per the one rule (no task files beside code).
