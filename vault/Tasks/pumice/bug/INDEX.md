<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# pumice — bugs

**Next ID: PUMICE-051** — never recycle a number, even when its item closed.

IDs here are the area's original `PUMICE-NNN` sequence, not a per-lane
one: these items predate the lanes and are referenced from 136 files.
The DIRECTORY carries the lane; the ID stays the stable handle. New
items continue the same sequence so a number means one thing in pumice.
**The sequence is SHARED ACROSS THE THREE LANES** -- compute Next ID
from the highest PUMICE-NNN anywhere in the area, not from this lane.
check_task_ids validates within a lane, so a per-lane maximum passes
the checker and still hands out a number another lane already owns.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its
state. Moving an item between states is `git mv`.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |

## Open

- **BUG-000** — reserved template; copy the file, do not file against it.
- **PUMICE-045** — one unattributed mismatched beat, seen once in 1008 matrix cells
