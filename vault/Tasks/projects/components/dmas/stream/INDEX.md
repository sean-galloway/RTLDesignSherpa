---
title: STREAM tasks
summary: Task rollup for the STREAM DMA component (projects/components/dmas/stream).
---

# STREAM tasks

**Next ID: TASK-093** — never recycle a number, even when its task closed.

## Lanes

This area tracks three kinds of work, each with its own lifecycle pages and its
own ID sequence. Pick the lane before filing:

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `TASK-001` |
| [bug/](bug/INDEX.md) | a defect with a reproduction | `BUG-001` |
| [issue/](issue/INDEX.md) | an anomaly/risk/question not yet diagnosed | `ISSUE-001` |

**The pages at this level are the LEGACY task lane.** They are frozen: close
them out where they stand, and do not add to them. New work of any kind goes in
a lane above. See [the convention](../../../../INDEX.md) for the full definitions.


Task numbers are scoped to THIS area. The same number exists in other areas and that is expected, not a collision -- amba's TASK-080 and this one are different tasks, and the area is what tells them apart. Cite one as "STREAM TASK-080" when writing outside this file.

Task tracking for the STREAM component (nested under `projects/components/dmas/`
to mirror the repo path). Lifecycle pages: [active](active.md) · [open](open.md)
· [closed](closed.md) · dropped (created when first needed). Convention:
[Tasks](../../../../INDEX.md).

## Active (in progress)
- **TASK-056** — RFC Stage-E in-core R/W datapath perf monitors (retire
  `axi_bus_meter`): RTL + cosim complete; board bring-up pending.

## Open (not started)
- **TASK-091** (Medium) — stream_core's formal DEPS rotted behind the monitor
  rework; 3 missing modules added, a 4th is where the chain was stopped.

- **TASK-092** (Medium) — datapath_wr_test proof FAILS (`ap_desc1_ready_state`)
  now that it elaborates; FORMAL_TODO's PASS was against a 2-month-stale flat.

- **TASK-090** (Medium) — `.sv2v_prep` holds 7 TRACKED generated files that
  `make clean` deletes; the mechanism behind the 376-insertion prep drift.

- **TASK-080** (Medium) — STREAM formal proofs read a hand-copied
  `gaxi_fifo_sync` (and an orphan package stub), not the RTL; convert
  them to flatten the real module with sv2v, as done for repo-root formal.

## Closed (done)

- **TASK-087** (Medium) — sv2v regen fixed: a missing `monitor_arbiter_pkg` in PKGS,
  then the `$display`/`$time` AST_AUTOWIRE. 4 units, not 2; Makefile-only.
  Done 2026-09-24.

- **TASK-084** (Low) — TB address->name lookup now inverts the generated
  regmap; 143/143 resolve, 0 UNKNOWN. The entry's original MON-offset
  diagnosis was wrong and is corrected in the closed entry. Done 2026-09-24.

- **TASK-089** (Medium) — RLB blocks gated; 26 entries / 18 RDLs total.
  pit_8254's regmap excluded as a finding. Done 2026-09-24.

- **TASK-088** (Medium) — regen gate extended 1 -> 9 RDL blocks (14 entries),
  semantic compare added; caught a ~2900-line stale doc. Done 2026-09-24.

- **TASK-083** (Medium) — `.rdl` edits now gated against their generated
  artifacts (hook + CI); proven to block a real commit. Done 2026-09-23.

- **TASK-086** (Medium) — perf FIFO now read non-empty; pop protocol AND
  data coherence asserted, proven to fail on the old datapath. Done 2026-09-23.

- **TASK-085** (Medium) — perf FIFO read made atomic: pop once BOTH halves
  are read; capture flop deleted. Done 2026-09-23.

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
