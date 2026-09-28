# TASK-029: move gen_pumice_signal_contracts.py onto bin/kmaps and arm its maps

**Status:** open 2026-09-27  **Priority:** P3 -- documentation evidence, no RTL
change. Filed from tooling TASK-006 when that global item closed: the shared
K-map emitter (`bin/kmaps/`) is done; what remains is pumice's own use of it.

## Part 1 -- the conversion (ready-made on a branch)

`docs/gen_pumice_signal_contracts.py` still carries a private copy of the writer,
minimiser and styles that stream retired on 2026-09-25. A converted version is
on branch `tooling-pumice-halves`, commit `e8fc555c4` (+ `b50495fde` for this
task's wording): 2068 -> 1848 lines, the four `axis_eqs=` lists folded into
`varnames` triples, and a 28-entry `CITES` registry gated by
`bin/kmaps/citations.py` -- the workbook had no citation check before. It was
verified the only way a refactor of a green workbook can be: a
layout-independent dump of every map (17 maps, 364 cells, relations,
expressions, 4 tables, 20 sheets) is identical old vs new, and
`check_kmap_rtl_sync.py` output is byte-identical (16 checked / 0 drifted / 1
not machine-checkable). Rebase it, regenerate, diff the workbook, push. Or
redo it by hand from the stream generator's shape; the branch is a starting
point, not a requirement.

## Part 2 -- plainly: the derived-vs-RTL gate is INERT on all 17 maps today

Once on the shared writer every pumice map renders `DEPENDS ONLY ON: not
stated` and `VERDICT: NOT CHECKED`, because no map ever supplied
`depends_only_on=` or `rtl_sop=`. Before the conversion the same was true but
invisible -- the old writer never asked. The relations, don't-cares, implicants
and the citation gate ARE live; the one defect-finding criterion (derived cover
vs the RTL as written) checks nothing. Treat NOT CHECKED the way TASK-028
taught: a map that is not gated is not evidence.

For each of the 17 `km.kmap(...)` calls:

1. `depends_only_on=`: why the function depends on the axes alone (what is
   held constant, which guards are folded into an axis, where the fold is).
2. `rtl_sop=`: the RTL expression as a sum-of-products over the axis names, so
   the emitter renders IDENTICAL / DIFFERS. A DIFFERS verdict is a finding --
   redundant RTL terms (say why they stay), an unstated invariant, or a bug --
   and goes to this lane's bug list, not smoothed over.

Multi-valued maps (the four with `values=`) get item 1 only; a minimal SOP is
undefined for them and the writer skips the verdict on purpose.

Spec: [[signal-contracts-and-kmaps]]. STREAM's equivalent is stream TASK-012.

Acceptance: generator imports `bin/kmaps`; regenerated workbook has no
`not stated` and no `NOT CHECKED` row; any DIFFERS is justified in the map's
check text or filed as a pumice BUG.
