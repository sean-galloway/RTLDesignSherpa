# TASK-002: RAPIDS-beats has NO contracts workbook at all
> **Was `RAPIDS-KMAP` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** open 2026-08-06  **Blocked on:** [[TOOLING-KMAP]] items 1-4

Unlike stream and pumice, RAPIDS has **no**
`docs/gen_signal_contracts_kmaps.py` whatsoever. So this is not "finish the
maps" -- it is "there are none". Given RAPIDS-beats was resynced FROM stream
(prefetch, commit-gating, recoverable-timeout all ported across), it inherits
stream's decision shapes without inheriting even stream's partial workbook.

Start by copying the stream generator once [[TOOLING-KMAP]] has promoted the
machinery to `bin/` -- copying it BEFORE that just creates a third private copy
to keep in step.

Targets specific to RAPIDS, in priority order. The first three are OPEN
known_issues, which makes them the highest-value maps in the repo:

1. **Sink data path -- AXI timeout detection missing**
   (`known_issues/active/sink_data_path.md`). A map of the timeout
   qualification cone would make the missing term visible as an axis with no
   contributing expression.
2. **Sink SRAM control -- single-read limitation**
   (`known_issues/active/sink_sram_control.md`). A read-issue qualification map
   with an honest `depends_only_on` is the direct statement of what the
   limitation IS.
3. **`drain_size_gt1` source beat drop**
   (`known_issues/active/drain_size_gt1_source_beat_drop.md`). Beat-drop bugs
   are adjacency bugs; this is the archetypal K-map target.
4. **`scheduler_beats` issue qualification + commit gating.** Ported from
   stream's scheduler, so it carries the same latch/clear and timeout shapes --
   and RAPIDS has no equivalent of stream's macro coverage to catch a
   divergence.
5. **`snk_data_path_axis_beats` credit/RDA accounting.** RAPIDS' network side
   has no counterpart in stream, so nothing stream proved transfers here. This
   is the part of RAPIDS most exposed by having no workbook.
6. **`alloc_ctrl_beats` / `drain_ctrl_beats`.** Same space-accounting shapes as
   stream items 5, but independently drifted since the resync.

Note the naming-conflict history (`known_issues/scheduler_group_signal_naming_
conflicts.md`): RAPIDS has already been bitten by two signals whose names
implied a relationship they did not have. That is the same failure mode the
axis-equation requirement (criterion 3) exists to catch.
