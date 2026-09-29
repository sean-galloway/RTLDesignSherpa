# TASK-030: repoint pumice's 173 legacy tracker-id citations

**Status:** closed 2026-09-27  **Priority:** P3. Filed from tooling TASK-013 when
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
`projects/components/mem-ctrl-ip/pumice-ddr2-lpddr2` and
`projects/fpga-systems/NexysA7/pumice`.

Acceptance: the count above is 0 by the same measurement, no bare-id rewrite
performed, lint unchanged on the 26 `.sv`.

---

## Done 2026-09-27 — 162 repointed, 9 left with no target

Swept with a map-keyed script (regex `(?<!was )\bPUMICE-(KMAP|[0-9]{3})\b`,
annotation form `pumice <NEW> (was <OLD>)`, the convention c50be80d7 used for
every other area). 36 map rows parsed, 875 tracked files in scope.

**162 citations repointed across 59 files**, 23 distinct legacy ids:

| ext | repointed |
|---|---:|
| `.py` | 91 |
| `.md` | 37 |
| `.sv` | 19 |
| `Makefile` | 9 |
| `.tcl` | 4 |
| `.toml` | 2 |

Heaviest: `PUMICE-037` -> `pumice BUG-014` x49, `PUMICE-025` -> `pumice BUG-011`
x15, `PUMICE-014` -> `pumice TASK-023` x11.

**Checks.** Line parity +161/-161 (no line added or removed; 162 edits because
two landed on one line). Every `.sv` change is inside a comment -- verified by
diffing with `-U0` and filtering for any changed line that is not `//`, `*` or
`/*`, which came back empty across all 11 touched `.sv`. `make lint` in
`rtl/`: PASS, Verilator 50 modules each as its own top, Verible clean, rc=0.
No bare-id rewrite performed (every legacy form here is `PUMICE-`-prefixed, so
the cross-area ambiguity the method warns about does not arise).

**The counts in "The count" above were wrong, twice.** The filed figure was 173
(104/43/26); measured at sweep time the total was 171. The `.sv` bucket was 24
citations, not 26, and the filed breakdown omitted `Makefile`, `.tcl` and
`.toml` entirely. Worse, my own first measurement said 169 -- because I measured
with the same regex I swept with (`PUMICE-(KMAP|[0-9]{3})`), so it could not see
`PUMICE-PERF`. A broader `PUMICE-[0-9A-Z]+` found it. A measuring regex that
shares its blind spot with the sweeping regex confirms the sweep against itself;
the check has to be wider than the edit.

**9 citations LEFT ALONE -- no migration target exists:**

| legacy id | count | where |
|---|---:|---|
| `PUMICE-018` | 7 | `rtl/fub/pumice_cmd_arbiter.sv` x5 (stage-1a snapshot register, in-flight ACT/PRE bank guard, live ACT-gate re-validation), `dv/tbclasses/pumice_cmd_arbiter_tb.py` x2 |
| `PUMICE-PERF` | 2 | `rtl/fub/pumice_cmd_arbiter.sv:455` (per-entry double-issue mask), `dv/tests/fub/test_pumice_arbiter_issue_rate.py:2` |

Neither has a row in `MIGRATION_MAP.md`, so neither can be repointed -- they name
work that was never in the flat tracker as its own item. They are load-bearing
comments (they explain why the arbiter has an extra pipeline stage and a
symmetric bank guard), so deleting the label would cost the explanation.
**This misses the stated acceptance ("the count above is 0").** Disposition needs
a decision, not a sweep: grandfather them as historical labels, or file real ids
for the snapshot-register and per-entry-issue work and repoint to those.
