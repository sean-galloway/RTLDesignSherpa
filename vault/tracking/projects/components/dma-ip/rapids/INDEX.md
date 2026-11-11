---
title: RAPIDS tasks
summary: Task rollup for the RAPIDS DMA component (projects/components/dma-ip/rapids).
---

# projects/components/dma-ip/rapids — task rollup

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`). Moving an item between states
is `git mv`, so an item is in exactly one state by construction.

## Lanes

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 5 | 0 | 40 | 1 | 0 |
| [bug/](bug/INDEX.md) | 1 | 0 | 17 | 1 | 0 |
| [issue/](issue/INDEX.md) | 1 | 0 | 7 | 0 | 0 |

Open counts include the reserved `-000` template in each lane, which is never a
real item. **Each lane carries its own `Next ID`** — see the lane INDEXes.

IDs are scoped to THIS area AND its lane: RAPIDS `BUG-001` and STREAM `BUG-001`
are different bugs. Cite one from outside as "RAPIDS BUG-001".

## Renamed 2026-09-24

Everything moved into the lanes and was renumbered into per-lane sequences.
The flat pages are gone. The component's own `TASKS.md` was folded in on
2026-11-07; its numbers collide with this lane's, so they map as:

| TASKS.md | Is |
|---|---|
| `TASK-001` | [BUG-018](bug/closed/BUG-018.md) |
| `TASK-003` | [TASK-042](task/closed/TASK-042.md) (residual [TASK-043](task/open/TASK-043.md)) |
| `TASK-011` | [TASK-040](task/closed/TASK-040.md) |
| `TASK-012` | [TASK-041](task/closed/TASK-041.md) |
| `TASK-002`, `-004`..`-009` | [TASK-044](task/dropped/TASK-044.md) (dropped, one disposition each) |

The 2026-09-24 renumbering, for the older IDs: Old numbers
appear in commit messages and handbook notes, so the map is kept:

| Was | Is |
|---|---|
| `RAPIDS-OBS` | [TASK-001](task/closed/TASK-001.md) |
| `RAPIDS-KMAP` | [TASK-002](task/closed/TASK-002.md) |
| `TASK-080` | [TASK-003](task/closed/TASK-003.md) |
| `TASK-086` | [ISSUE-001](issue/closed/ISSUE-001.md) |
| `TASK-057` | [TASK-004](task/closed/TASK-004.md) |
| `TASK-084` | [TASK-005](task/closed/TASK-005.md) |
| `TASK-083` | [TASK-006](task/closed/TASK-006.md) |
| `TASK-081` | [BUG-001](bug/closed/BUG-001.md) |
| `TASK-082` | [BUG-002](bug/closed/BUG-002.md) |
| `TASK-085` | [ISSUE-002](issue/closed/ISSUE-002.md) |

`RAPIDS-KMAP` is blocked on [[TOOLING-KMAP]] and `TASK-003` on the qc/humanize
pass; both stay in `open/` with the blocker stated in the body, since the lanes
carry no `deferred/` state.
