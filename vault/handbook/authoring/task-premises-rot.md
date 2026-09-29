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
| it sidesteps a shared-primitive bug | the bug (amba BUG-034, was AMBA-HISTCH1) was fixed at source a day after the task was filed; and the sidestep was never real -- it described another consumer's parameterization |
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
`vault/Tasks/pumice-ddr2-lpddr2/task/dropped/TASK-025.md`.


## A cross-item link encodes the OTHER item's state, and breaks on its move

Related to the above, and the same shape: a tracker entry's *links* are claims
with a timestamp too, and unlike its prose these ones DO go red -- just not in
the session that broke them.

Items live in state directories (`open/`, `active/`, `closed/`, `dropped/`,
`deferred/`), and moving between states is a `git mv`. A relative link from one
item to another therefore encodes the target's state in its path. Close one of
the pair and the link breaks:

```
# written while both were in open/ -- a valid sibling link
[pumice TASK-015](TASK-015.md)

# TASK-016 git mv'd to closed/, TASK-015 still open -> now broken
[pumice TASK-015](../open/TASK-015.md)     # the repair
```

**Either direction does it**: moving the file that holds the link, or moving the
file it points at. The second is worse, because the session that closes
TASK-015 has no reason to be looking at TASK-016.

This is not an argument for bare `[[wikilinks]]`. Those never break because the
checker does not resolve them -- and they are ambiguous repo-wide, since the same
ID exists in several lanes (four `BUG-003.md`, four `TASK-015.md`). Resolving a
bare `[[BUG-003]]` from a pumice directory landed on `tooling/`. Precision and
durability genuinely trade off here; the path form is right, and the cost is that
it needs maintaining.

**What to do:** after any `git mv` between state directories, grep the moved
file's links and check each one FROM ITS NEW DIRECTORY before committing:

```
cd <new state dir>
for l in $(grep -oE '\]\([^)h][^)]*\)' ITEM.md | tr -d '])('); do
    [ -e "$l" ] && echo "OK   $l" || echo "BROKEN $l"
done
```

The tree-wide link ratchet is the backstop and it is loud -- `bin/check_broken_links.py`
blocks the commit. But it blocks it for EVERY session, not just yours: a peer
working elsewhere in the vault hit this red gate and had to commit with
`--no-verify` while measuring that their own files contributed nothing, until the
one broken link was repaired. A shared gate that one session breaks is one every
session pays for, so repair it at the move rather than at the next commit.
