<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# pumice — task rollup

DDR2/LPDDR2 memory controller
(`projects/components/memory-controllers/pumice-ddr2-lpddr2/`).

**There are no flat pages in this area any more.** `open.md`, `active.md`,
`closed.md` and `dropped.md` were removed on 2026-09-27; their 35 historical
`PUMICE-NNN` items became one file per item in the lanes below. Until then this
area was HYBRID -- lanes for live work, flat pages for history -- and this file
used to promise that any `PUMICE-NNN` absent from its rename table "stays where
it is, in the flat closed.md / dropped.md". That promise is retired;
[vault/Tasks/MIGRATION_MAP.md](../MIGRATION_MAP.md) is now how an old number
resolves, and every migrated file carries a provenance line naming its legacy ID.

**Each lane carries its own Next ID** — see the lane INDEXes
([task](task/INDEX.md), [bug](bug/INDEX.md), [issue](issue/INDEX.md)).
Do not recycle an ID, in any lane, ever.

## Lanes

**Every item is its own file**, `<ID>.md`, under the directory for its state
(`open/`, `active/`, `closed/`, `dropped/`, `deferred/`). Pick the lane before
filing; IDs are per-lane sequences.

| Lane | For | open | active | closed | dropped |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | 2 | 0 | 22 | 4 |
| [bug/](bug/INDEX.md) | a defect with a reproduction | 1 | 0 | 17 | 1 |
| [issue/](issue/INDEX.md) | an anomaly/risk/question not yet diagnosed | 1 | 0 | 10 | 3 |

Counts INCLUDE each lane's `NNN-000` template, which lives in `open/` -- that is
the repo-wide convention, and reading it the other way is how three of this
area's counts went wrong on 2026-09-27.

## What is actually open

Nothing in bug or issue. In task, one real item plus the template:

- **[TASK-015](task/open/TASK-015.md)** — test the DUT across configurations: a
  4-layer plan (reset-parity gate, pairwise covering array x gap, invariant
  oracles, seeded soak) with a reportable 2-way coverage number. Layers 1 and 3
  are now largely delivered by the 12 named DRAM operating points and the
  scheduler-layer JEDEC matrix; what remains is layer 0 (reset parity) and
  layer 2b (telemetry invariants).

The correctness backlog is EMPTY: BUG-001, BUG-002 and BUG-003 are all closed,
and BUG-003 -- an arbiter pick that its own final safety gate had rejected being
pushed to the DRAM anyway -- was fixed 2026-09-27.

## Legacy ID resolution

Two renames have happened in this area. Both are recorded, because a
`PUMICE-NNN` in a commit message or an RTL comment has to resolve to exactly one
thing.

**2026-09-24 — the then-OPEN items moved into the lanes:**

| Was | Is | | Was | Is |
|---|---|---|---|---|
| PUMICE-006 | [TASK-001](task/closed/TASK-001.md) | | PUMICE-045 | [BUG-001](bug/closed/BUG-001.md) |
| PUMICE-013 | [TASK-002](task/closed/TASK-002.md) | | PUMICE-030 | [ISSUE-001](issue/dropped/ISSUE-001.md) |
| PUMICE-023 | [TASK-003](task/dropped/TASK-003.md) | | PUMICE-046 | [ISSUE-002](issue/closed/ISSUE-002.md) |
| PUMICE-029 | [TASK-004](task/dropped/TASK-004.md) | | PUMICE-047 | [ISSUE-003](issue/closed/ISSUE-003.md) |
| PUMICE-034 | [TASK-005](task/closed/TASK-005.md) | | PUMICE-048 | [ISSUE-004](issue/closed/ISSUE-004.md) |
| PUMICE-035 | [TASK-006](task/closed/TASK-006.md) | | | |
| PUMICE-039 | [TASK-007](task/closed/TASK-007.md) | | | |
| PUMICE-049 | [TASK-008](task/closed/TASK-008.md) | | | |
| PUMICE-CLEANUP | [TASK-009](task/closed/TASK-009.md) | | | |

**2026-09-27 — the 35 historical flat items moved too.** Full table in
[MIGRATION_MAP.md](../MIGRATION_MAP.md). Lane assignment was hand-derived from
each item's own Status line, because a keyword pass misclassified 14 of the 35.

`PUMICE-045..050` are RETIRED, not free: 045-049 are in the table above and
every commit message before 2026-09-24 still refers to them by the old number.
The highest legacy number ever issued in this area is 050.

**Legacy IDs were not rewritten at their call sites.** Measured after the
migration: 652 `PUMICE-*` occurrences repo-wide, but 327 of those are this
tracker's own cross-references and provenance lines. The real debt is the **238
outside `vault/Tasks/`** -- 151 `.py`, 46 `.md`, 39 `.sv`, 2 `.rdl`, over 29
distinct legacy IDs. Only 39 are RTL comments; the bulk is DV and host Python.
Rewriting RTL to chase a tracker rename costs more than it gains, so old
references resolve through the tables here and in
[MIGRATION_MAP.md](../MIGRATION_MAP.md). tooling TASK-013 tracks the debt.

An earlier version of this file said 533. That was measured with a
`PUMICE-[0-9]{3}` pattern -- which cannot match `PUMICE-KMAP`, the one legacy ID
here whose suffix is a word -- and before this migration added citations of its
own. Scope from the 238, not from either of the bigger numbers.

## ID reuse, resolved 2026-09-06 (kept: the numbers are still cited)

An early series and a later one collided on three numbers. All three were
renumbered to unique IDs in 2026-09-06, with every reference updated in the same
pass. **Read the arrows carefully: each of 010, 011 and 012 names TWO different
things** -- the LATER item that wrongly reused the number, and the ORIGINAL item
that legitimately held it. Both senses appear in old commit messages.

| Number | The LATER item that reused it | The ORIGINAL item that held it |
|---|---|---|
| 010 | per-worker sim_builds / seed echo -> renumbered `PUMICE-019` -> [BUG-009](bug/closed/BUG-009.md) | addr-map single knob -> [TASK-021](task/closed/TASK-021.md) |
| 011 | AMBA-HISTCH1 + multiid hist accounting -> renumbered `PUMICE-020` -> [BUG-010](bug/closed/BUG-010.md) | LPDDR2 MR init -> [TASK-022](task/closed/TASK-022.md) |
| 012 | greppable structure trackers -> renumbered `PUMICE-015` -> [TASK-024](task/closed/TASK-024.md) | LPDDR2 write-AP dropped writes -> [BUG-008](bug/closed/BUG-008.md) |

So a bare `PUMICE-010` in text written after 2026-09-06 means the addr-map task
([TASK-021](task/closed/TASK-021.md)); before that date it may mean either, and the surrounding
sentence is the only disambiguator.

The 008 observer renumber also stands: the observer task became `PUMICE-016`
([TASK-025](task/dropped/TASK-025.md)), and the only `PUMICE-008` is the dropped per-beat deskew
task ([TASK-019](task/dropped/TASK-019.md)).

Do not recycle an ID, in any lane, ever.

---

Practice and rationale live in the [handbook](../../handbook/INDEX.md); this
directory tracks *work* only. `/GLOBAL_REQUIREMENTS.md` wins on conflict.
