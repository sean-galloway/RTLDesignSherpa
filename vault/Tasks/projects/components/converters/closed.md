<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# converters — Closed

---

## CONV-003 — dnsize DUAL buffer: dropped beats and misplaced LAST
**Status:** closed OBSOLETE 2026-08-23 — the mode was removed rather than fixed

The defects were real and confined to `DUAL_BUFFER=1`: 36 of 40 beats under
backpressure, and LAST landing early in two other scenarios. Single buffer
was clean throughout.

Nothing instantiated it. Both wrappers hardwired `.DUAL_BUFFER(0)` and a
repo-wide search found no `DUAL_BUFFER(1)` anywhere; the only thing
exercising the path was the test grid, sweeping it out of habit.

It had also stopped earning its place. Dual buffer existed from the initial
commit to cover a real single-buffer throughput gap, and `281de52c`
(2026-05-21) closed that gap by making the single buffer accept its
replacement during the last narrow beat -- the same commit wired both
wrappers to `DUAL_BUFFER(0)`. Measurement confirms there is nothing left to
recover: 0.992 beats/cycle either way.

So the choice was to debug a broken mode nobody used and that measured no
faster, or delete it. Deleted: 186 lines of generate logic, the parameter,
both wrapper pass-throughs, 8 test configurations, a doc chapter and its
diagram.

Both scenarios gated on account of this (`test_burst_tracking`,
`test_backpressure`) are asserted again and green -- DUAL configs were the
only ones failing them.

**If dual buffering is ever wanted again:** it is in git history at
`40e5e116~1`, and it was broken when removed. Reviving it means debugging
it, not restoring it.

