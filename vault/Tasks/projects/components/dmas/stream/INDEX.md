---
title: STREAM tasks
summary: Task rollup for the STREAM DMA component (projects/components/dmas/stream).
---

# projects/components/dmas/stream — task rollup

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`). Moving an item between states
is `git mv`, so an item is in exactly one state by construction.

## Lanes

| Lane | For | Open | Active | Closed | Dropped |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | 4 | 1 | 7 | 0 |
| [bug/](bug/INDEX.md) | a defect with a reproduction | 2 | 0 | 9 | 0 |
| [issue/](issue/INDEX.md) | an anomaly/risk/question not yet diagnosed | 1 | 0 | 0 | 1 |

Open counts include the reserved `-000` template in each lane, which is never a
real item. **Each lane carries its own `Next ID`** — see the lane INDEXes.

Task numbers are scoped to THIS area AND to its lane: `BUG-001` here and
`BUG-001` in rapids are different bugs, exactly as `TASK-080` already named two
different tasks in two areas. Cite one from outside as "STREAM BUG-001".

## Renamed 2026-09-24

Everything moved into the lanes and was renumbered into per-lane sequences.
The flat pages (`open.md`, `active.md`, `closed.md`, `dropped.md`) are now
pointers and take no new items. Old numbers appear in commit messages and
handbook notes, so the map is kept:

| Was | Is |
|---|---|
| `STREAM-KMAP` | [TASK-001](task/closed/TASK-001.md) |
| `STREAM-MONREGS` | [TASK-002](task/closed/TASK-002.md) |
| `TASK-079` | [TASK-003](task/open/TASK-003.md) |
| `TASK-056` | [TASK-004](task/active/TASK-004.md) |
| `TASK-080` | [BUG-001](bug/closed/BUG-001.md) |
| `TASK-090` | [BUG-002](bug/closed/BUG-002.md) |
| `TASK-091` | [BUG-003](bug/closed/BUG-003.md) |
| `TASK-089` | [TASK-005](task/closed/TASK-005.md) |
| `TASK-088` | [TASK-006](task/closed/TASK-006.md) |
| `TASK-083` | [TASK-007](task/closed/TASK-007.md) |
| `TASK-086` | [TASK-008](task/closed/TASK-008.md) |
| `TASK-058` | [TASK-009](task/closed/TASK-009.md) |
| `TASK-060` | [TASK-010](task/closed/TASK-010.md) |
| `TASK-092` | [BUG-004](bug/closed/BUG-004.md) |
| `TASK-087` | [BUG-005](bug/closed/BUG-005.md) |
| `TASK-084` | [BUG-006](bug/closed/BUG-006.md) |
| `TASK-085` | [BUG-007](bug/closed/BUG-007.md) |
| `TASK-073` | [BUG-008](bug/closed/BUG-008.md) |
| `TASK-081` | [BUG-009](bug/closed/BUG-009.md) |
| `TASK-059` | [BUG-010](bug/closed/BUG-010.md) |
| `TASK-082` | [ISSUE-001](issue/dropped/ISSUE-001.md) |
| `(un-IDed heading)` | [TASK-011](task/closed/TASK-011.md) |

`TASK-003` is blocked on the qc/humanize pass and stays in `open/` with the
blocker stated in the body, since the lanes carry no `deferred/` state.
`STREAM-KMAP` (now TASK-001) was closed 2026-09-25 -- its TOOLING-KMAP
dependency was discharged locally by porting `relations=` plus an invariant
checker into stream's own generator rather than waiting on shared tooling.
