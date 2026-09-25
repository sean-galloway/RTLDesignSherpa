# TASK-002: RAPIDS-beats has NO contracts workbook at all
> **Was `RAPIDS-KMAP` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** in progress -- workbook created 2026-09-25, item 3 DONE  
**Unblocked:** the shared machinery was promoted to `bin/kmaps/` (TOOLING-KMAP item 5), so the generator builds on it rather than forking a third private copy.

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

---

## Progress 2026-09-25

`projects/components/dmas/rapids/docs/gen_rapids_signal_contracts_kmaps.py`
now exists, built on the shared `bin/kmaps` package (no private copy of the
machinery). Run it with `source env_python && python3
docs/gen_rapids_signal_contracts_kmaps.py`; it writes
`rapids_signal_contracts.xlsx`.

**Item 3 (`drain_size_gt1` source beat drop) -- DONE.** Two sheets:
"Contracts src drain" (the drain interface, 5 rows) and "K-maps src drain"
(3 computed maps + a STREAM/RAPIDS comparison table). All six criteria
discharged:

1. *Computed cells* -- every grid evaluated from a python mirror; verified by
   reading the fills back out of the workbook (GREEN 17 / GREY 15 / DC 8,
   matching an independent recomputation).
2. *Defined ordering* -- Gray order, inherited from the shared writer.
3. *Axis equations + citations* -- 32 citations, all grep-verified at build
   time; a mutation test (a deliberately wrong line number) confirmed the gate
   actually fails rather than passing blind.
4. *Sufficiency argument* -- stated per map in `check`.
5. *Don't-cares marked X with citation* -- 8 unreachable cells in map 1, from
   two `relations=` predicates; a mutation test (a deliberately vacuous
   predicate) confirmed the invariant checker rejects it.
6. *Derived implicants vs RTL verdict* -- `rtl_sop=` on all three maps.

**The map found the bug.** Map 1 carries `fifo_ge_size` as an axis that does
not appear in the RTL expression at all -- the missing-term shape this task
predicted would be useful. Its single green cell at `fifo_ge_size=0` is the
defect: the grant is qualified on an availability view that double-counts beats
held in the latency bridge. Mechanism, citations, git archaeology and a
candidate one-line fix are now in
`known_issues/active/drain_size_gt1_source_beat_drop.md`. It turns out to be a
STREAM defect RAPIDS inherited in 2026-01 and STREAM fixed in 2026-07
(`e8908eebf`) without a back-port.

Also answered while here: **item 3's open question about the SINK path.**
`snk_sram_controller_unit_beats.sv:229` is the identical unfixed line, so the
sink shares the defect. That overlaps item 5's territory.

### Remaining

- Items 1-2 re-filed against the beats RTL on 2026-09-25 (the cited signals no
  longer exist); they need re-scoping before mapping.
- Items 4, 5, 6 not started.
