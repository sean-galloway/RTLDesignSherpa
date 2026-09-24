<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# pumice — tasks

**Next ID: PUMICE-051** — never recycle a number, even when its item closed.

IDs here are the area's original `PUMICE-NNN` sequence, not a per-lane
one: these items predate the lanes and are referenced from 136 files.
The DIRECTORY carries the lane; the ID stays the stable handle. New
items continue the same sequence so a number means one thing in pumice.
**The sequence is SHARED ACROSS THE THREE LANES** -- compute Next ID
from the highest PUMICE-NNN anywhere in the area, not from this lane.
check_task_ids validates within a lane, so a per-lane maximum passes
the checker and still hands out a number another lane already owns.

Planned work we decided to do: a feature, a refactor, a migration, a cleanup. It starts from INTENT -- nothing is wrong, we want something different.

Each item is **its own file**, `<ID>.md`, inside the directory for its
state. Moving an item between states is `git mv`.

| State | Count | What |
|---|---|---|
| [open/](open/) | 10 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |

## Open

- **PUMICE-006** — QoS + advanced scheduling (post-cleanup)
- **PUMICE-013** — characterize + tune the advanced modes (all three axes)
- **PUMICE-023** — the char-framework sim is the board gate and must run before any pumice RTL commit
- **PUMICE-029** — pumice is AT REST: what a future session needs to know
- **PUMICE-034** — the paging predictors are built unconditionally and the board never uses them
- **PUMICE-035** — no stall-cause attribution, so the overhead breakdown cannot be published
- **PUMICE-039** — batch same-direction columns to amortise the R/W turnaround
- **PUMICE-049** — no test bounds the write drain, and the cap is unreachable at the shipped watermarks
- **PUMICE-050** — doc + filelist cleanup (push from workstation)
- **TASK-000** — reserved template; copy the file, do not file against it.
