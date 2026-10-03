<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# pumice — task rollup

DDR2/LPDDR2 memory controller
(`projects/components/mem-ctrl-ip/pumice-ddr2-lpddr2/`).

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
| [task/](task/INDEX.md) | planned work we decided to do | 3 | 0 | 30 | 4 |
| [bug/](bug/INDEX.md) | a defect with a reproduction | 1 | 0 | 20 | 1 |
| [issue/](issue/INDEX.md) | an anomaly/risk/question not yet diagnosed | 1 | 0 | 16 | 3 |

Counts INCLUDE each lane's `NNN-000` template, which lives in `open/` -- that is
the repo-wide convention, and reading it the other way is how three of this
area's counts went wrong on 2026-09-27.

## What is actually open

**Bug lane: BUG-022** — the `ADDR_MAP.bank_lsb` documented lower bound is
too permissive by log2(DFI_RATE); an RDL-comment/header trap for the
first bank-interleaving user, not live misbehavior (every build ships
ROW_MAJOR).

**Task lane: TASK-035, TASK-037, TASK-038.** TASK-035 finishes tier-1
formal coverage (5 of 27 blocks; wr_data_cam counterexample + dfi_cdc
name resolution remain). TASK-037 reconciles 16 stale dv/testplans (29
broken refs) plus a parser check. TASK-038 rebuilds the ddr2-char
harness images with the fixed sdpram slave and repins pumice board perf
— board-gated, batch with stream TASK-016.

**Issue lane: ISSUE-020** — the paging perf assertions are calibrated
against pre-compliant tFAW/tRRD window behavior and the gate fails on
them in combinations; re-pin (Sean's call) or fund a skid/bypass.
Surfaced closing BUG-021 2026-10-03.

The correctness backlog is otherwise EMPTY: BUG-021 (proved tRRD
violation) was fixed 2026-10-03 — fire-stage window enforcement,
formally armed and mutation-checked.

TASK-033 (the v2/v3 deferrals) is in `task/deferred/`, parked pending the
DDR3/LPDDR3 project rather than dropped.

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

`PUMICE-045..051` are RETIRED, not free: 045-049 are in the table above and
every commit message before 2026-09-24 still refers to them by the old number.
The highest legacy number ever issued in this area is **051**.

**The legacy ID space is now fully numeric.** Two IDs in this area were once
word-suffixed, and both have been numbered retroactively:
`PUMICE-CLEANUP` -> `PUMICE-050` (2026-09-24) and `PUMICE-KMAP` ->
`PUMICE-051` (2026-09-27). A word-suffixed ID does not sort, does not parse
against a `PREFIX-NNN` checker, and gets silently skipped by any tool that
assumes digits -- `PUMICE-KMAP` was dropped by exactly such a parser during the
flat-page migration and only recovered because a peer session's independent count
disagreed. Both spellings still resolve; new text should use the number.

`PUMICE-PERF` is NOT an ID and is not numbered: it is an informal work-stream
label on two comments (`pumice_cmd_arbiter.sv`, `test_pumice_arbiter_issue_rate.py`)
marking the Phase 1 per-entry issue-mask work. It has no tracker item and never
did. If it ever needs one, file it in a lane with a lane ID rather than
retrofitting a legacy number.

**Legacy IDs were not rewritten at their call sites.** The sweep is **173
citations** -- 104 `.py`, 43 `.md`, 26 `.sv`, 0 `.rdl`, over 27 distinct legacy
IDs. Only the 26 RTL comments are risky; the rest is DV and host Python plus
prose. tooling TASK-013 tracks it.

Bigger numbers are in circulation and all of them over-count. Of 663 `PUMICE-*`
occurrences on disk, 339 are this tracker's own provenance lines and map rows
(they ARE the resolution mechanism) and 152 are inside a git worktree at
`.claude/worktrees/pumice-ataglance-modes` -- a transient checkout of this same
repo on its own branch. **A repo with a worktree holds two copies of everything**,
so check `git worktree list` before quoting any repo-wide count. Earlier
revisions of this file said 533 and then 238; see
[MIGRATION_MAP.md](../MIGRATION_MAP.md) for why each was wrong.

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
