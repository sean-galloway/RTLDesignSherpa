# TASK-010: Cohesive SKILLS strategy for the repo

> Migrated 2026-09-27 from `vault/Tasks/tooling/closed.md` as **TOOL-013** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-08-09 (migrated from /TOOLING_TODO.md item 2, opened
2026-07-22; the work happened in the weeks between and the tracker never
caught up)

Wanted: repo-resident skills every agent/session discovers automatically,
replacing methodology scattered across CLAUDE.md files, bin/*.md how-tos and
fragile assistant memory. Proposed `.claude/skills/<name>/SKILL.md`.

**Verified done, and beyond the original list.** `.claude/skills/` exists and
carries every candidate skill from the proposal — doc-methods, kmaps,
uart-harness (sim and FPGA halves merged into one), hard-design, rds-dv-bfms,
filelists, review-rounds — plus the ones the model grew into: coverage,
formal, fsm-discipline, module-docs, rds-dv-axes, rds-dv-randomization,
regressions, signal-prefixes, tasks, test-review, doc-placement. The open
decisions resolved the way the vault settled them: skills are SIGNPOSTS
pointing at canonical handbook notes (vault/handbook/INDEX.md), method detail
lives in the handbook, GLOBAL_REQUIREMENTS.md stays the enforcement authority
(owner decision 2026-07-22, preserved). The "skill pointers must not rot"
verification wish is the one piece with no enforcement today — if that
becomes real work, open it fresh.

---
