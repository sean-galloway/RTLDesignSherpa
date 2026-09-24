# reed-solomon — task rollup

**Next ID: RS-002** — never recycle a number, even when its task closed.

## Lanes

This area tracks three kinds of work, each with its own lifecycle pages and its
own ID sequence. Pick the lane before filing:

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `TASK-001` |
| [bug/](bug/INDEX.md) | a defect with a reproduction | `BUG-001` |
| [issue/](issue/INDEX.md) | an anomaly/risk/question not yet diagnosed | `ISSUE-001` |

**The pages at this level are the LEGACY task lane.** They are frozen: close
them out where they stand, and do not add to them. New work of any kind goes in
a lane above. See [the convention](../../../INDEX.md) for the full definitions.


Future `projects/components/reed-solomon/` component. No RTL, DV or PRD
exists yet — this area holds the intent so it does not vanish when
COMMON-009 (BCH/Reed-Solomon ECC as library work) was dropped 2026-08-09.

| Page | Count | What |
|---|---|---|
| [active.md](active.md) | 0 | in progress right now |
| [open.md](open.md) | 1 | accepted, not started |
| [closed.md](closed.md) | 0 | done (kept for history) |
| [dropped.md](dropped.md) | 0 | ended without completing |

## Open shortlist

- **RS-001** — stand up the Reed-Solomon component (PRD first; scope decision
  BCH-in-or-out; own DV area). Waits on a real consumer.
