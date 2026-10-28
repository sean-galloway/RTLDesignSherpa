---
title: jet-mesi-l1 tasks
summary: Task rollup for the jet lockup-free MESI L1 cache component (projects/components/cache-ip/jet-mesi-l1) — amber's non-blocking MSHR upgrade.
---

# projects/components/cache-ip/jet-mesi-l1 — task rollup

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`). Moving an item between states
is `git mv`, so an item is in exactly one state by construction.

jet reuses the shared core at `cache-ip/common-ip` (l1_*) unchanged; work on
the shared core itself files in the amber-mesi-l1 or common-ip lanes, not
here.

## Lanes

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 1 | 0 | 0 | 0 | 0 |
| [bug/](bug/INDEX.md) | 0 | 0 | 0 | 0 | 0 |
| [issue/](issue/INDEX.md) | 0 | 0 | 0 | 0 | 0 |

Counts exclude the reserved `-000` template in each lane. **Each lane
carries its own `Next ID`** — see the lane INDEXes.

Task numbers are scoped to THIS area AND to its lane. Cite one from outside as
"jet-mesi-l1 TASK-001".

## Created 2026-10-28

Area created when the J1–J7 PRD decisions closed (Sean) and the design spec
(`docs/superpowers/specs/2026-10-28-jet-mshr-design.md`) was written; first
task is the implementation itself. Area created with all three lanes so the
checker always has a parseable lane.
