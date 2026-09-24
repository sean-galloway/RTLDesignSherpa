<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# pumice — issues

**Next ID: PUMICE-051** — never recycle a number, even when its item closed.

IDs here are the area's original `PUMICE-NNN` sequence, not a per-lane
one: these items predate the lanes and are referenced from 136 files.
The DIRECTORY carries the lane; the ID stays the stable handle. New
items continue the same sequence so a number means one thing in pumice.
**The sequence is SHARED ACROSS THE THREE LANES** -- compute Next ID
from the highest PUMICE-NNN anywhere in the area, not from this lane.
check_task_ids validates within a lane, so a per-lane maximum passes
the checker and still hands out a number another lane already owns.

An anomaly, risk, or open question not yet diagnosed. It RESOLVES INTO a bug, a task, or a recorded no-action.

Each item is **its own file**, `<ID>.md`, inside the directory for its
state. Moving an item between states is `git mv`.

| State | Count | What |
|---|---|---|
| [open/](open/) | 4 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |

## Open

- **ISSUE-000** — reserved template; copy the file, do not file against it.
- **PUMICE-030** — read latency is ~2x LiteDRAM's, and it caps small-burst reads
- **PUMICE-046** — close-page modes reach only ~63% of their own command-bus ceiling
- **PUMICE-048** — the +25-30% batching gain was measured with the broken drain

## Closed

- **PUMICE-047** — SCHED_WR_WM.wr_batch_max may clobber the whole register on write
