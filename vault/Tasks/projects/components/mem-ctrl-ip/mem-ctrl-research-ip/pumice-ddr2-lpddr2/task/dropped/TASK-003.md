# TASK-003: the char-framework sim is the board gate and must run before any pumice RTL commit
> **Was `PUMICE-023` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** DROPPED 2026-09-25 (content moved, see below) — was open 2026-09-08  **Priority:** P1

`ddr2_char_framework/dv/tests` (test_ddr2_char_uart + test_ddr2_char_char) is
the only suite that builds the board's x16 / strict-timing configuration. The
arbiter fix passed all 213 pumice fub/macro/top tests and failed 7 there
(write side, fixed by the write-staged gate). Its Makefile `run-all-*` targets
were being swallowed by the `run-%` pattern into a nonexistent test id, so the
area had silently stopped gating; aliases added 2026-09-08. Pre-existing
failures to triage: `smoke_rate2_faithful`, `smoke_rate2_rdphase1`,
`smoke_rate2_strict`, `pagehit_rate2_x16_free_earlyen` (all fail at
79fb58a66, before this session). Add this directory to the pumice regression
convention (`regressions` skill) and to the components master Makefile.


## 2026-09-25 — DROPPED as a task; the content MOVED, it was not discarded

Sean: *"if a task can't be closed, that means it is a rule that should be
elsewhere."* This was never a work item — it had no completion condition, so
it would have sat in the open lane forever, inflating the count and training
readers to skim it.

Content now lives at: **vault/handbook/dv/running-regressions.md ("Some areas have a gate the module suite cannot be")**

Dropped here rather than closed, because "closed" implies work finished. No
work was done; the record moved to where the repo's own convention says it
belongs (area facts beside the code, method in the handbook — see the root
CLAUDE.md).
