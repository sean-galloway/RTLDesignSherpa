<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# Tooling tasks — active (in progress)

## TOOL-001: Migrate the remaining areas into /vault/Tasks/<area>/
**Priority:** P2
**Status:** In Progress (2026-07-22; checklist reconciled 2026-09-18) —
5 areas migrated, 6 pending, and 3 source files this list had never named.
The batch is still NOT started: the two decisions below are unanswered.
**Owner:** Claude (assist) / Sean (review)

**Goal:** Move every remaining per-component TASKS.md / TODO.md into the central
`/vault/Tasks/<area>/` structure so all project status is visible from one place, and
retire the scattered files. Use the `tasks` skill's "Migrating an area"
procedure for each so they all come out identical.

**Areas still pending** (tracked at their old files until moved):
- [x] common — rtl/common/TASKS.md (DONE 2026-07-23 -> vault/Tasks/common/)
- [ ] stream — dmas/stream/TASKS.md + TODO_RFC_StageE_datapath_perfmon.md
- [ ] rapids — dmas/rapids/TASKS.md + docs/rapids_beats_mas/TODO.md
- [x] bridge — bridge/TASKS.md (DONE -> vault/Tasks/bridge/; source gone)
- [ ] delta — delta/TASKS.md
- [ ] hive — hive/TASKS.md
- [x] retro-legacy — DONE 2026-09-25 -> vault/Tasks/RLB/hpet/ (all six items were
      HPET; TASK-001 closed, TASK-002 filed as BUG-001, the rest as TASK-002..005).
      The rtl/{ioapic,pm_acpi,smbus}/TODO.md files named here no longer exist.
- [ ] memory-controllers — ddr3-lpddr3 / ddr4-lpddr4 TASKS.md (pumice DONE 2026-07-23 -> vault/Tasks/pumice/)
- [x] nexysa7 — DONE -> vault/Tasks/nexysa7/. NOTE: the timing_characterization
      TASKS.md named here was not migrated with it -- the area moved to
      projects/asic-trials/ and its file is still live (see below).
- [ ] formal — formal/FORMAL_TODO.md
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
- [ ] asic-trials/timing_characterization/TASKS.md — 9 task blocks, live
      2026-09-08. Formerly under NexysA7; the area moved, the file did not.
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
