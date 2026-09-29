# ISSUE-002: task areas are named two different ways for the same kind of thing

**Priority:** P3 — cosmetic until someone has to guess, which is every time a new
component area is created.
**Status:** CLOSED 2026-09-28 (resolution below)
**Owner:** TBD
**Found by:** renaming `ddr3-lpddr3/` to `scoria-ddr3-lpddr3/` to match
`pumice-ddr2-lpddr2/`, which made the tracker inconsistency visible.

## The inconsistency

The memory-controller family is one kind of thing with one naming convention --
each IP carries an igneous-rock codename that is "the RTL identifier prefix, the
directory name and the module/package prefix"
(`projects/components/mem-ctrl-ip/README.md`). Their TASK AREAS do not
follow it, and do not agree with each other:

| Component directory | Task area | Shape |
|---|---|---|
| `pumice-ddr2-lpddr2/` | `vault/Tasks/pumice/` | top level, codename |
| `scoria-ddr3-lpddr3/` | `vault/Tasks/memory-controllers/ddr3-lpddr3/` | nested, protocol name |
| `andesite-…` (future DDR4) | `vault/Tasks/memory-controllers/ddr4-lpddr4/` | nested, protocol name |

So pumice's tracker is `pumice` and scoria's is `memory-controllers/ddr3-lpddr3`.
Both patterns are in use, for sibling IPs, and a new area has no way to tell which
is intended.

## Why it was not just fixed alongside the rename

Renaming a task area is `check_task_ids.py`'s business: the area name appears in
`vault/Tasks/INDEX.md`, in every lane `INDEX.md`, in the `--next <area>/<lane>`
invocation the templates tell you to use, and in commit messages and RTL comments
that cite items by area. It is a mechanical sweep, but it is a sweep, and it is
the kind that wants to happen once for the whole family rather than twice.

## The decision

1. **Promote scoria and andesite to match pumice** — `vault/Tasks/scoria/`,
   `vault/Tasks/andesite/`, retiring the `memory-controllers` grouping (which
   `vault/Tasks/INDEX.md` already describes as a "grouping dir, holds no items").
   Consistent with the README's "the codename IS the identifier" rule and with
   the only board-validated member.
2. **Demote pumice to match them** — `vault/Tasks/memory-controllers/pumice/`.
   Cheaper to argue for grouping, far more expensive to execute: pumice has 60+
   items and is cited by ID across RTL comments, commit messages and the
   handbook.
3. **Leave it and write the rule down**, saying explicitly that the grouping is
   for un-started IPs and an area graduates to top level when it has RTL. That is
   arguably what happened by accident, and it is defensible — but it needs to be
   stated, or the next person guesses again.

Option 1 is the consistent one and the sweep is small while scoria and andesite
hold two real items between them. It gets more expensive every time either
accumulates history, which is the argument for deciding now rather than later.

---

## Closed 2026-09-28 -- the COMPOUND name, everywhere a directory names an IP

Sean's decision: use `pumice-ddr2-lpddr2` as the directory name, **not** the bare
codename `pumice` and **not** the bare protocol pair `ddr2-lpddr2`. None of the
three options as filed was quite it -- option 1 would have produced
`vault/Tasks/scoria/`, which is the bare codename -- so the rule is the compound
form, applied at every level where a directory names one of these IPs.

### What moved

| Level | Before | After |
|---|---|---|
| component dir | `pumice-ddr2-lpddr2/` | unchanged (already compound) |
| | `ddr3-lpddr3/` | `scoria-ddr3-lpddr3/` |
| | `ddr4-lpddr4/` | `andesite-ddr4-lpddr4/` |
| task area | `vault/Tasks/pumice/` | `vault/Tasks/pumice-ddr2-lpddr2/` |
| | `vault/Tasks/memory-controllers/ddr3-lpddr3/` | `vault/Tasks/scoria-ddr3-lpddr3/` |
| | `vault/Tasks/memory-controllers/ddr4-lpddr4/` | `vault/Tasks/andesite-ddr4-lpddr4/` |
| knowledge mirror | keyed by repo path | follows the component dir automatically |

So the second inconsistency this issue named -- one area top level, two nested --
is resolved as well: all three are top level now, matching the only member that
had live work. `vault/Tasks/memory-controllers/` survives as a plain directory
holding only `ADVANCED_MODES_ROADMAP.md`, which spans the whole family and
therefore belongs to none of its members. `bin/check_task_ids.py` passes at 86
areas.

### The rule is written where it will be read

`projects/components/mem-ctrl-ip/README.md` states it outright now rather
than leaving it to be inferred from the directories that happen to exist, which is
what made it ambiguous: the codename is the RTL/module/package prefix, the
DIRECTORY is the compound form, and the bare codename stays the prose form.

### What was deliberately NOT rewritten

**The ~111 files citing items as "pumice TASK-034" in prose.** The convention that
an ID must name its area ([[feedback_task_ids_need_their_area]] -- never a bare
`TASK-077`) is satisfied by the codename, which is unambiguous since no other area
starts with `pumice`. Rewriting 111 files of prose to gain nothing was not worth
the churn or the risk of a bad substitution, and the README now says the bare
codename is the prose form on purpose rather than by neglect.

`vault/Tasks/MIGRATION_MAP.md` IS updated -- 36 rows -- because its Area column is
how a legacy `PUMICE-NNN` resolves to a live location, and a stale value there
stops the map doing its one job. Closed and dropped items that merely narrate
history keep their original wording; only path references were repointed, so links
resolve.
