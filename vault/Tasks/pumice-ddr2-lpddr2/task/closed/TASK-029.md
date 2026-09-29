# TASK-029: give the 17 signal-contract maps their sufficiency argument and RTL verdict

**Status:** CLOSED 2026-09-28  **Priority:** P3 -- documentation evidence, no RTL
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

---

## Closed 2026-09-28

All 17 maps now carry `depends_only_on=`, and the 14 two-valued ones carry
`rtl_sop=`. The workbook has **no `not stated` row and no `NOT CHECKED` row**:

    DEPENDS ONLY ON rows : 17   (every map)
    VERDICT IDENTICAL    : 12
    VERDICT DIFFERS      :  2   (both justified in the map's check text)

`check_kmap_rtl_sync.py`: 16 mirrors checked, 0 drifted, 1 not machine-checkable
-- unchanged, as expected for a documentation pass with no RTL change.

### The two DIFFERS are real findings, and the answer is the same both times

`rd_act_m[e]` -- RTL is
`!row_active & !guarded & act_ready & tfaw_ok & trrd_ok & !rfc_busy`; the derived
minimal cover drops `!row_active`.

`rd_pre_m[e]` -- RTL is `row_active & !guarded & !hit & pre_ready`; the derived
cover drops `row_active`.

In both cases the literal is FREE because the map's own relations prove the
readiness signal already implies it: `safe_act_o` is ANDed with `!r_row_valid`
(`bank_timer.sv:133`), so `act_ready => !row_active`; `safe_pre_o` is ANDed with
`r_row_valid`, so `pre_ready => row_active` (and `hit => row_active`
independently). Half of each grid is unreachable, the minimiser is free to use
those cells, and the literal drops out.

**The terms stay, and the maps now say why.** The arbiter re-states an invariant
that lives inside `bank_timer` rather than depending on another module's
internals: if the timer ever reported ready with the row in the wrong state,
that AND is what still blocks the command. Redundant by derivation, deliberate
by design -- not a defect, so nothing is filed as a BUG.

That is the criterion-6 gate doing exactly what it is for. It was INERT on all
17 maps before this; now 14 are armed, and the first thing it did was surface a
cross-module implication that was true but nowhere written down.

### Two corrections to this task's own text

* It says "the four with `values=`". There are **three** (`refresh-branch
  action`, `w_out_ready / w_fire_out`, `state_o`), so 14 maps take a verdict,
  not 13.
* It predicted the conversion would leave the citation gate happy. On its first
  run after landing it FAILED -- two `file:line` citations into
  `pumice_mem_cmd_scheduler.sv` were off by two lines, because the pumice
  session had added `stat_row_hit_o` to that file for BUG-020 hours earlier.
  Repointed 527->529 and 574->576. The gate working on its first contact with
  live code is the best evidence for it that this task could have produced.
