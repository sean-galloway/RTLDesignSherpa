<!-- Managed by the `tasks` convention: see /Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# Tooling tasks — active (in progress)

### TOOL-001: Migrate the remaining areas into /Tasks/<area>/
**Priority:** P2
**Status:** 🟡 In Progress (2026-07-22) — amba pilot done; 13 areas pending.
**Owner:** Claude (assist) / Sean (review)

**Goal:** Move every remaining per-component TASKS.md / TODO.md into the central
`/Tasks/<area>/` structure so all project status is visible from one place, and
retire the scattered files. Use the `tasks` skill's "Migrating an area"
procedure for each so they all come out identical.

**Areas still pending** (tracked at their old files until moved):
- [ ] common — rtl/common/TASKS.md
- [ ] stream — dmas/stream/TASKS.md + TODO_RFC_StageE_datapath_perfmon.md
- [ ] rapids — dmas/rapids/TASKS.md + docs/rapids_beats_mas/TODO.md
- [ ] bridge — bridge/TASKS.md
- [ ] bch — bch/TASKS.md
- [ ] delta — delta/TASKS.md
- [ ] hive — hive/TASKS.md
- [ ] retro-legacy — retro_legacy_blocks/TASKS.md + rtl/{ioapic,pm_acpi,smbus}/TODO.md
- [ ] memory-controllers — pumice / ddr3-lpddr3 / ddr4-lpddr4 TASKS.md
- [ ] nexysa7 — timing_characterization/TASKS.md + cdc_counter_display CDC_DEMO_TODO.md
- [ ] formal — formal/FORMAL_TODO.md
- [ ] coverage — val/COVERAGE_TODO.md
- [ ] tooling — TOOLING_TODO.md (this area's own backlog; migrate alongside)

**Per area (see `tasks` skill):** fence-aware split of the source into task
blocks → classify open/active/closed/dropped by REAL repo state (not the stale
Status marker) → write INDEX + the four pages → repoint inbound refs → delete
originals → verify block count + links against the original.

**Open decisions to confirm with Sean before starting the batch:**
1. Is open/active/closed/dropped the right lifecycle split?
2. Area granularity: group the 3 memory-controllers vs split; retro-legacy
   sub-blocks (ioapic/pm_acpi/smbus) as one area vs several?
