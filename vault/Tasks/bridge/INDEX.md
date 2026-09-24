# bridge — task rollup

**Next ID: BRIDGE-020** — never recycle a number, even when its task closed.

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
a lane above. See [the convention](../INDEX.md) for the full definitions.


Bridge crossbar generator (`projects/components/bridge/`): the CSV/toml-driven
generator, its generated wrappers/xbars/adapters, and their DV.

| State | Count |
|---|---|
| [active](active.md) | 0 |
| [open](open.md) | 0 |
| [closed](closed.md) | 21 |
| [dropped](dropped.md) | 0 |

## Open

Nothing, since 2026-09-13. BRIDGE-017 (the legacy backlog: perf
characterization, synthesis flow, CDC slave ports, QoS aging, registered
crossbar) and BRIDGE-018 (native-AXI5 fabric: Memory Tagging and chunking
through the structs) both closed; the two known Wishbone gaps are on the
dropped page by the owner's decision (best effort). A new bridge task starts
from a consumer's need, not from this list.

> The pre-migration `projects/components/bridge/TASKS.md` was folded in on
> 2026-09-10: ledger at the end of [closed](closed.md), leftovers in
> BRIDGE-017 and [dropped](dropped.md). The file is retired.

Practice and rationale live in the [handbook](../../handbook/INDEX.md);
this directory tracks *work* only. `/GLOBAL_REQUIREMENTS.md` wins on conflict.
