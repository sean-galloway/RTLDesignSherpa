# TASK-029: give the 17 signal-contract maps their sufficiency argument and RTL verdict

**Status:** open 2026-09-27  **Priority:** P3 -- documentation evidence, no RTL
change. Filed by the tooling session when `gen_pumice_signal_contracts.py` moved
onto the shared `bin/kmaps` machinery (tooling TASK-006 item 5).

## What changed underneath

`docs/gen_pumice_signal_contracts.py` no longer carries its own K-map writer,
minimiser and styles; it imports `KmapWriter` from `bin/kmaps/writer.py` and
runs the citation gate (`bin/kmaps/citations.py`) over a `CITES` registry of
the 28 `file:line` quotes its maps make. The workbook's cells, relations and
expressions are unchanged -- verified cell for cell (17 maps, 364 cells) against
the old writer -- and `check_kmap_rtl_sync.py` reports the same 16 checked / 0
drifted / 1 not machine-checkable.

The shared writer renders two things the old one never asked for, and every
pumice map now shows them as HONEST GAPS rather than silently omitting them:

- `DEPENDS ONLY ON: not stated -- this map is a SLICE with no sufficiency
  argument` -- the old writer's `relations=` say which cells are unreachable,
  but not why the mapped function ignores every input NOT on the axes.
- `VERDICT: NOT CHECKED -- supply rtl_sop= to diff the RTL against the derived
  cover` -- the minimal sum-of-products is derived from the grid, but with no
  `rtl_sop=` there is nothing to diff it against, so the one criterion that
  finds defects (RTL-differs) is unarmed.

## Plainly: the derived-vs-RTL gate is INERT on all 17 maps today

Not "content to add later" -- the workbook's one defect-finding check (criterion
6, derived cover vs the RTL as written) currently checks nothing on any pumice
map, and the sufficiency argument (criterion 3) is absent on all 17. Before the
conversion the same was true but invisible, because the old writer never asked;
now it is printed on every map. The relations, don't-cares, implicants and the
citation gate ARE live. Treat NOT CHECKED the way pumice TASK-028 (was PUMICE-051) / TASK-028 taught:
a map that is not gated is not evidence.

## The work

For each of the 17 `km.kmap(...)` calls:

1. `depends_only_on=`: one sentence saying why the function depends on the
   axes alone (what is held constant, which other guards are folded into an
   axis, and where that fold is written).
2. `rtl_sop=`: the RTL expression as a sum-of-products over the axis names,
   so the emitter renders IDENTICAL / DIFFERS. A DIFFERS verdict is a finding
   -- either redundant RTL terms (say why they stay) or an unstated invariant
   or a bug -- and belongs in this lane's bug list, not smoothed over.

Multi-valued maps (the four with `values=`) get item 1 only; a minimal SOP is
undefined for them and the writer skips the verdict on purpose.

Spec and the six criteria: [[signal-contracts-and-kmaps]]. STREAM did the same
pass for its five priority maps under STREAM TASK-001; 26 of its 37 still
render NOT CHECKED, so this is not a pumice-only gap.

Acceptance: the regenerated workbook has no `not stated` and no `NOT CHECKED`
row, and any DIFFERS verdict is either justified in the map's check text or
filed as a pumice BUG.
