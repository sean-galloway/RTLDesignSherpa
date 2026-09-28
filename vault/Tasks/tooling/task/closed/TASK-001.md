# TASK-001: Migrate the remaining areas into /vault/Tasks/<area>/

> Migrated 2026-09-27 from `vault/Tasks/tooling/active.md` as **TOOL-001** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P2
**Status:** CLOSED 2026-09-27. Every box is ticked and, more to the point,
the goal moved past this checklist: the vault now has **zero flat pages anywhere**,
not merely no stray TASKS.md files. Measured at HEAD on close:

    flat per-state pages          0
    items one-file-per-item     408   (241 task, 141 bug, 26 issue)
    areas with lane dirs         33
    deferred/ directories        95   (one per lane; the state was legal but
                                      unrepresentable before 808603a6e)
    MIGRATION_MAP.md rows       270   across 18 areas

This task was filed as "move the remaining TASKS.md/TODO.md into vault/Tasks".
That part finished on 2026-09-25. What closed it was the second, larger half nobody
had written down: 16 areas were still keeping their items as `## <ID>` blocks inside
shared open/active/closed/dropped pages, ~265 items in 67 files. Those were split one
file per item and their legacy IDs renumbered into the per-lane namespaces, on Sean's
decision (2026-09-27) to renumber rather than preserve. pumice migrated its own 36 as
the last area; verified here against HEAD, 36/36 resolve to committed files.

**What it cost, recorded because the next migration will hit the same things.**
Every one of these was caught by a gate, not by reading:
  - A keyword classifier guessing task-vs-bug from item bodies labelled "scrub the
    tests" and "Migrate the remaining areas" as defects. Thrown away; lanes assigned
    by hand from titles, defaulting to task as hive and delta had.
  - Numbering from 001 collided with pre-existing lane items and SKIPPED MATH-002
    while its source page was deleted. Recovered from the committed blob; a
    pre-flight inventory of existing IDs is now part of the procedure.
  - Moving a body two directories deeper breaks relative links three ways: `../`
    chains, links to the area's own flat page (which was CROSS-LANE, so pointing at
    <lane>/<state>/ resolves but narrows the meaning), and bare relative paths.
  - `git commit -- <dir>` commits the WORKTREE copy, so a directory pathspec sweeps
    peers' edits; and a pathspec built from a `git status` snapshot dropped 19 staged
    deletions, leaving 20 IDs in two states at HEAD while local gates passed. Build
    the pathspec from `git diff --cached`, and verify with `git show HEAD:<p> | cmp`.

**Left open deliberately:** the renumbering's citation debt, filed as tooling
TASK-013 -- legacy IDs are still cited from RTL comments, DV code, formal harnesses,
the handbook and board records. MIGRATION_MAP.md plus each file's provenance line are
what make an old ID resolvable; the sweep is a separate mechanical job.

**One row above is wrong and TASK-013 does not cover it:** `nexysa7` is ticked, but
its seven open items are misfiled -- four are pumice work, one belongs to
asic-trials/timing_characterization, one names a deleted `projects/NexysA7/
stream_characterization` path, and one describes the rehome that has already happened.
Migrating an area proved nothing about whether its items belonged there. Raised with
Sean 2026-09-27, who chose to DELETE the area outright rather than rehome the items;
done 2026-09-27.

**Owner:** Claude (assist) / Sean (review)

**Goal:** Move every remaining per-component TASKS.md / TODO.md into the central
`/vault/Tasks/<area>/` structure so all project status is visible from one place, and
retire the scattered files. Use the `tasks` skill's "Migrating an area"
procedure for each so they all come out identical.

**Areas still pending** (tracked at their old files until moved):
- [x] common — rtl/common/TASKS.md (DONE 2026-07-23 -> vault/Tasks/common/)
- [x] stream — DONE. TASKS.md was folded in earlier; its flat pages (open/active/
      closed/dropped.md, all item-free by then) were retired in da5a84eb0. Items
      live at vault/Tasks/projects/components/dmas/stream/.
- [x] rapids — DONE. Same shape as stream: TASKS.md folded in earlier, the two
      item-free flat pages retired in da5a84eb0. Items live at
      vault/Tasks/projects/components/dmas/rapids/.
- [x] bridge — bridge/TASKS.md (DONE -> vault/Tasks/bridge/; source gone)
- [x] delta — DONE 2026-09-25 -> vault/Tasks/projects/components/delta/ (16 items;
      TASK-001/002 closed on migration -- their acceptance criteria are met in
      ch02_blocks/ while the ch04_routing/ and ch05_flow_control/ paths they name
      do not exist; real TASK-000 renumbered TASK-016). File deleted.
- [x] hive — DONE 2026-09-25 -> vault/Tasks/projects/components/hive/ (25 items, all
      open but TASK-025; zero .sv, zero tests, only ch01 + ch02/00 written, so every
      Related Files path is still unwritten). File deleted.
- [x] retro-legacy — DONE 2026-09-25 -> vault/Tasks/RLB/hpet/ (all six items were
      HPET; TASK-001 closed, TASK-002 filed as BUG-001, the rest as TASK-002..005).
      The rtl/{ioapic,pm_acpi,smbus}/TODO.md files named here no longer exist.
- [x] memory-controllers — DONE 2026-09-25 (pumice DONE 2026-07-23 -> vault/Tasks/pumice/).
      This row contradicted the two [x] entries below it for four days; corrected.
- [x] nexysa7 — migrated, then the AREA WAS DELETED 2026-09-27 (its items were misfiled;
      see the note below). Originally -> vault/Tasks/nexysa7/. NOTE: the timing_characterization
      TASKS.md named here was not migrated with it -- the area moved to
      projects/asic-trials/ and its file is still live (see below).
- [x] formal — DONE 2026-09-25, and the answer is NO AREA. All five open items were
      stale: amba TASK-090/091/092/093 closed 2026-09-11 (see vault/Tasks/amba/closed.md)
      and formal/stream/Makefile has existed since 2026-09-18. Zero open items, so
      creating vault/Tasks/formal/ would assert a backlog that does not exist. The five
      boxes were corrected in place; the file STAYS -- eleven vault/handbook pages cite
      it by full path and its content is measured status + findings history, not tasks.
- [x] coverage — val/COVERAGE_TODO.md — DONE 2026-08-09: classified against
      the tree (most had landed via the tests.mk/cov_utils consolidation);
      vault/Tasks/coverage/ created with COV-000 (closed, the record) and
      COV-001 (open, the 3 areas still off base tests.mk). File deleted.
- [x] tooling — TOOLING_TODO.md — DONE 2026-08-09: item 1 (kmap promote)
      was already subsumed by TOOLING-KMAP step 5; item 2 (skills strategy)
      verified done -> TOOL-013 closed; item 3 (Scripts link rot,
      re-verified still broken) -> TOOL-014 open. File deleted, referrers
      repointed.

**Files this checklist never listed** (found 2026-09-18 by sweeping the tree
for stray TASKS.md / TODO*.md, which is how the list should have been built):
- [x] asic-trials/timing_characterization/TASKS.md — DONE 2026-09-25 ->
      vault/Tasks/projects/asic-trials/timing_characterization/. It held FOUR task
      blocks, not the 9 recorded here. TASK-001 filed with its PARTIAL state
      measured (Vivado sweep + parser + CSV exist under different names; Quartus
      Tcl and the example config do not). File deleted, referrers repointed.
- [x] memory-controllers/ddr3-lpddr3/TASKS.md — DONE 2026-09-25 (1 block; it was a
      stub) -> vault/Tasks/memory-controllers/ddr3-lpddr3/
- [x] memory-controllers/ddr4-lpddr4/TASKS.md — DONE 2026-09-25 ->
      vault/Tasks/memory-controllers/ddr4-lpddr4/

ddr3/ddr4 are exactly decision 2 below: `vault/Tasks/` has a `pumice` area but
no memory-controllers grouping, so there is nowhere agreed for them to go.

**Per area (see `tasks` skill):** fence-aware split of the source into task
blocks → classify open/active/closed/dropped by REAL repo state (not the stale
Status marker) → write INDEX + the four pages → repoint inbound refs → delete
originals → verify block count + links against the original.

**Open decisions — BOTH ANSWERED 2026-09-25, batch unblocked:**
1. ~~Is open/active/closed/dropped the right lifecycle split?~~ **Yes (Sean).**
2. ~~Area granularity~~ **ANSWERED 2026-09-25 (Sean):** group the memory
   controllers (pumice stays at vault/Tasks/pumice/, the only one with live
   work); RLB is an area that ALSO has sub-areas, one per block, created on
   demand rather than scaffolded.
