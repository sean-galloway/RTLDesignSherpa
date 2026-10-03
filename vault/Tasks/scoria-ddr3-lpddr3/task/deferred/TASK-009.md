# TASK-009: Deferred advanced scheduling / refresh modes for DDR3/LPDDR3

Seeds carried forward from TASK-001's survey. Each is parked behind the unblock condition recorded in `docs/superpowers/specs/2026-10-03-scoria-advanced-modes-design.md` §6.

**Priority:** P3 — not on the board bring-up critical path.
**Status:** DEFERRED 2026-10-03.
**Owner:** TBD

## RAIDR (retention-aware refresh)

Unblock condition (spec §6): *a retention-profiling path exists (board or model) to feed per-row/bin data; Bloom-filter bin hardware is its own design.*

Controller-side work is the variable per-row/bin refresh interval scheduler once the profile is available. Do not start before the profiling path is defined.

## ChargeCache

Unblock condition (spec §6): *BUG-003 timing headroom — it makes the arbiter cone hotter, the opposite of what the 100 MHz closure needs now.*

The mechanism shortens tRCD/tRAS for recently-closed rows by tracking row addresses and their charge state. Re-evaluate only after `scoria_top` meets the 100 MHz design point.

## PARA / Rowhammer targeted refresh

Unblock condition (spec §6): *after a bitstream exists, with a Rowhammer test methodology; adjacency tracking is its own design.*

Probabilistic adjacent-row refresh as a scheduling policy. Requires both a bitstream-level Rowhammer test and a design for tracking aggressor/adjacent-row relationships.

## SALP (Subarray-Level Parallelism)

Unblock condition (spec §6): *belongs to andesite (DDR4/LPDDR4) per the task's own split.*

SALP overlaps accesses to different subarrays of the same bank; it is model-only for DDR3/LPDDR3 and belongs in the DDR4/LPDDR4 controller scope.

## Self-refresh / power-down scheduling

Unblock condition (spec §6): *reverses the recorded 2026-09-30 HAS decision (dormant `powerdown_ctrl`/`dfi_signal_pack`); re-opened only by the owner.*

This mode is explicitly excluded by the 2026-09-30 HAS decision. It may be re-opened only by the owner of that decision.

## Done when

- Each deferred item either unblocks and is moved to `open/`, or is dropped with a recorded reason.
- The area `INDEX.md` and `task/INDEX.md` counts stay consistent (`bin/check_task_ids.py` green).
