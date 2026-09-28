# TASK-030: repoint pumice's 173 legacy tracker-id citations

**Status:** open 2026-09-27  **Priority:** P3. Filed from tooling TASK-013 when
that global item closed: every other area's citations are swept (c50be80d7 hand-
written, 89536ba8e generator + regen); pumice's were excluded by decision because
its files were under active edit from this lane's worktree.

## The count

173 citations in tracked pumice files still name pre-migration ids: 104 `.py`,
43 `.md`, 26 `.sv`, 0 `.rdl` (measured with `git ls-files`; the 651 that
circulated was a worktree double-count plus the tracker's own provenance lines
-- run `git worktree list` before quoting any repo-wide number).

## The method (the same one every other area used)

Key every rewrite as `<area> <OLD>` -> `<area> <NEW>` against
`vault/Tasks/MIGRATION_MAP.md`; annotation form `<area> <NEW> (was <OLD>)`.
Never rewrite a bare `TASK-nnn` / `PUMICE-nnn` with no area -- four areas have a
TASK-015 and several a BUG-003. The 26 `.sv` comment edits are the only ones
with any risk (a comment-only diff, but check lint on the touched files); the
147 DV/host Python and markdown are mechanically safe. The tooling session's
sweep script (`id_sweep.py`, map-keyed, skips bare ids and rows whose target no
longer exists) is described in tooling TASK-013 and can be re-run scoped to
`projects/components/memory-controllers/pumice-ddr2-lpddr2` and
`projects/fpga-systems/NexysA7/pumice`.

Acceptance: the count above is 0 by the same measurement, no bare-id rewrite
performed, lint unchanged on the 26 `.sv`.
