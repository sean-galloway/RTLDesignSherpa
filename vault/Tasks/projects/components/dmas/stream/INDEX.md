---
title: STREAM tasks
summary: Task rollup for the STREAM DMA component (projects/components/dmas/stream).
---

# STREAM tasks

Task tracking for the STREAM component (nested under `projects/components/dmas/`
to mirror the repo path). Lifecycle pages: [active](active.md) · [open](open.md)
· [closed](closed.md) · dropped (created when first needed). Convention:
[Tasks](../../../../INDEX.md).

## Active (in progress)
- **TASK-056** — RFC Stage-E in-core R/W datapath perf monitors (retire
  `axi_bus_meter`): RTL + cosim complete; board bring-up pending.

## Open (not started)
- **TASK-073** (Medium) — build-mon host walks the `slvmon_apb` window with
  `slvmon_device`'s map, but that window is `u_slave_observer/obs_regs_top`
  now. Unrelated maps at the same offsets, so it silently writes wrong fields.
  Fix: retarget the host at obs_regs; the orphaned `slvmon_regs` set then
  deletes.
- **TASK-058** (High) — Signal contracts + K-maps for the significant STREAM
  signals (especially the read/write engines) to prove the design correct by
  construction.
- **TASK-060** (High) — Kick STREAM from its own registers: delete the sideband
  `i_kick_burst_mask/addr` ports and the dead `apb4todescr` path, replace with a
  FUB that drives the descriptor handshake from 64-bit cfg registers, gated on a
  write-only KICK_ENABLE bit per channel.

## Closed (done)
- **TASK-059** (High) — Fixed the extended chained strided (transpose) descriptor
  corruption: gated the run-base generator start on `w_is_ext` in `scheduler.sv`.
  Repro `test_stream_top_extended_chained_transpose` now passes. See
  [known_issues/resolved/extended_chained_transpose.md](../../../../../../projects/components/dmas/stream/known_issues/resolved/extended_chained_transpose.md).

The component's old `TASKS.md` / `TODO_*.md` next to the code are being retired
into this area per the one rule (no task files beside code).
