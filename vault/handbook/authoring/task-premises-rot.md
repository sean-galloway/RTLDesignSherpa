---
title: A parked task's justification has a shelf life
summary: Before executing a long-parked task, re-verify the premises in its body. They rot silently while the task sits, and the tracker never notices. PUMICE-016 sat ACTIVE on five premises, all of which had become false.
---

# A parked task's justification has a shelf life

A task entry is written once, at the moment someone understood the problem.
Everything it asserts about the tree -- what a module contains, which bug is
open, what a change would touch -- is a **claim with a timestamp**, and the
tracker has no mechanism to notice when the tree moves out from under it.
Nothing goes red. The task just sits there looking authoritative, and the
longer it sits the more authoritative it looks.

So: **before executing a task that has been parked for weeks, re-verify its
premises against the tree.** Not the goal -- the premises. Budget an hour for
it on anything that has aged. Finding the task is moot is a cheaper outcome
than building the thing.

## The case (PUMICE-016, 2026-08-26 -> dropped 2026-09-23)

Headed `ACTIVE ... now the DIRECTED path, not a nicety`, carrying a direct
quote from the owner. Four weeks later every load-bearing claim in it was
false, and each had been falsified by *ordinary unrelated progress*:

| The task said | What had happened |
|---|---|
| retire the harness's "hand-rolled" meters | they were never hand-rolled -- they are the shared `axi_bus_meter` / `axi_perf_latency_hist`, the same blocks the replacement wraps |
| it sidesteps a shared-primitive bug | the bug (AMBA-HISTCH1) was fixed at source a day after the task was filed; and the sidestep was never real -- it described another consumer's parameterization |
| it touches the bridge map | the bridge slot had been pre-reserved for it three weeks earlier |
| the owner directed "no perf logic inside the controller" | already true; the logic was in the harness the whole time |
| it unifies the throughput definition | already unified -- same primitive on both sides |

The task also gated another task on a correctness argument
(`land 016 first or the numbers carry the accounting error`) that had stopped
being true when the primitive was fixed. **A stale premise does not stay
local; it propagates as a dependency and blocks work that was never actually
blocked.** Check what a parked task gates, not just the task.

Measured outcome of building it anyway: +208% area (2030 -> 6253 LUTs) on a
part at 60.7% utilisation, for zero capability that was not already present.

## What re-verification looks like

Cheap, mechanical, and it is the same discipline as [[checkable-claims]] --
a claim in a task body is evidence the same way a number in a doc is:

- **Every "it is hand-rolled / bespoke / duplicated"** -> `find` the module and
  read the instantiation. Wrappers around shared blocks read as bespoke from
  the outside.
- **Every "this works around bug X"** -> check X's current state. A fix at
  source deletes the whole justification.
- **Every "this touches / requires / regenerates Y"** -> look at Y. Groundwork
  laid for the task may already be done.
- **Every quoted direction from the owner** -> check whether the tree already
  complies. The direction can be satisfied without the task.
- **Anything the task gates** -> re-check the gating argument separately.

Then close the loop with a measurement rather than an argument: the residue
PUMICE-016 carried was a red test arm, and re-running it (64/64, clean) is what
made the drop safe rather than merely reasoned.

## Record the finding, do not just abandon

Drop the task *with the evidence in it* -- premise by premise, with the
measurement. A task deleted quietly gets re-proposed on the same reasoning by
the next person who has the same good idea. See the entry in
`vault/Tasks/pumice/dropped.md`.
