---
title: jet-prime-mesi-l1 tasks
summary: Task rollup for jet-prime (projects/components/cache-ip/jet-prime-mesi-l1) — jet forked whole on 2026-11-12 to be made faster than OpenHW HPDcache on the single-cache rig; jet itself is frozen as the measured baseline.
---

# projects/components/cache-ip/jet-prime-mesi-l1 — task rollup

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`). Moving an item between states
is `git mv`, so an item is in exactly one state by construction.

jet-prime is jet (RTL, DV, formal) copied at commit 2be919254 with the
`jet_prime_` prefix. It reuses the shared core at `cache-ip/common-ip` (l1_*)
unchanged, exactly as jet does; work on the shared core files in the
amber-mesi-l1 or common-ip lanes, not here. jet's own lanes stay closed: jet
is the baseline the comparison report measured, and nothing in it moves.

## Lanes

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 0 | 1 | 0 | 0 | 0 |
| [bug/](bug/INDEX.md) | 0 | 0 | 0 | 0 | 0 |
| [issue/](issue/INDEX.md) | 0 | 0 | 0 | 0 | 0 |

Counts exclude the reserved `-000` template in each lane. **Each lane
carries its own `Next ID`** — see the lane INDEXes.

Task numbers are scoped to THIS area AND to its lane. Cite one from outside as
"jet-prime TASK-001".

## Created 2026-11-12

Area created when Sean asked for a jet-prime and for step 1 of the
"what will it take to beat HPDcache" plan (the reference comparison,
`projects/components/cache-ip/docs/reference_l1_comparison.md`, had jet 40 %
behind HPDcache on the 64 KB read-lean thrash at depth 16 with a serial miss
path as the diagnosis). Area created with all three lanes so the checker
always has a parseable lane.
