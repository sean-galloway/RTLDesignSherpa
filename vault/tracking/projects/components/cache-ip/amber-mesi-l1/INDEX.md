---
title: amber-mesi-l1 tasks
summary: Task rollup for the amber MESI L1 cache component (projects/components/cache-ip/amber-mesi-l1), whose shared core lives at cache-ip/common-ip (l1_*).
---

# projects/components/cache-ip/amber-mesi-l1 — task rollup

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`). Moving an item between states
is `git mv`, so an item is in exactly one state by construction.

Cross-cutting cache-IP work (shared `l1_*` core, jet, onyx, basalt) files
here when it concerns amber's own DV/verification closure; component-level
work for the siblings gets its own area under cache-ip/ when it starts.

## Lanes

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 0 | 0 | 1 | 0 | 0 |
| [bug/](bug/INDEX.md) | 2 | 0 | 1 | 0 | 0 |
| [issue/](issue/INDEX.md) | 0 | 0 | 0 | 0 | 0 |

Counts exclude the reserved `-000` template in each lane. **Each lane
carries its own `Next ID`** — see the lane INDEXes.

Task numbers are scoped to THIS area AND to its lane. Cite one from outside as
"amber-mesi-l1 BUG-001".

## Created 2026-10-12

First items filed from the FULL grid v2 post-mortem (BUG-001, BUG-002:
pre-existing FULL-soak corners, deterministic by seed, reproduced on the
pre-refactor tree). Area created with all three lanes so the checker always
has a parseable lane.
