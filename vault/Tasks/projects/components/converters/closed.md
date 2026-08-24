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

---

## CONV-004 — downsize converters truncate AWLEN/ARLEN on long bursts
**Status:** closed FIXED 2026-08-24 — burst splitting on both paths

Both dwidth converters multiplied the slave burst's beat count into the
8-bit length field, wrapping on long bursts: at 2:1 a full 256-beat burst
lost half its data; at 4:1 a 128-beat burst delivered FOUR beats of 512.
Reads timed out short the same way.

Fixed by splitting one slave burst into master bursts of <= 256 beats.
Write path: AW state machine + a split queue (one memory, two read
pointers) feeding per-burst WLAST framing and a worst-case-wins B fold.
Read path: same AR machine plus a one-bit final-flag queue; the only
R-side change is masking m_axi_rlast out of the upsize except on the
final master burst -- safe because 256 narrow beats is a whole number of
wide beats at every ratio.

RED/GREEN on both paths against the committed RTL. The write check
verifies FRAMING (AW lengths, burst legality, WLAST positions), not beat
count -- on the broken RTL all the data still arrived and a count-only
check passed, which is how the unit level stayed blind.

`make run-all-full-parallel`: **112 passed, 0 failed** -- previously
109/3, with the 3 (chain params 6/7/8) never having passed.

The first attempt (2026-08-23, reverted) and what it taught are in the
task history above the work list; the single-counter W framing it tried
is exactly what the split queue replaces.

