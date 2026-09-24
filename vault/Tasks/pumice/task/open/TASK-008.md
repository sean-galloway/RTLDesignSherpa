# TASK-008: no test bounds the write drain, and the cap is unreachable at the shipped watermarks
> **Was `PUMICE-049` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** open 2026-09-24  **Priority:** P3 — coverage gap plus a usability
finding; nothing is broken, the knob just cannot act where it ships

Residue of [[ISSUE-003]], which disproved the clobber. Two parts.

**A. `wr_batch_max` has no test that bounds the drain.** The arbiter fub TB
pins `sched_wr_high_wm_i = 0` (batching off), so the whole batching path --
drain, cap, `r_rd_owed` hysteresis -- is uncovered at fub level. The top-level
gen_replica cells exercise it but cannot ASSERT the bound, only the outcome.

A first attempt at a fub test is instructive and is why this is filed rather
than fixed: holding all 8 write slots schedulable with `low_wm=0` (so the
occupancy exit can never fire) produced 40 consecutive write columns at
`batch_max=1` -- which looks like the cap failing, but instrumenting
`r_wr_drain` showed it armed on only 1 of 40 cycles. Writes were winning for
an unrelated reason and the cap was never engaged, so the assertion was firing
on a premise the stimulus had not established. A valid test must PROVE the
drain is armed before it can claim anything about the bound.

**B. The cap is unreachable at the shipped watermarks.** `w_batch_done` is one
of three drain exits, and `w_wr_occ <= sched_wr_low_wm_i` is independent of it.
At hi=8/lo=4 the drain ends after ~4 writes, so the default cap of 16 never
binds: `wr_batch_max` only acts when it is below `(wr_high_wm - wr_low_wm)`.
Measured: at hi=8/lo=4, batch_max 16 and 0 are indistinguishable; at hi=8/lo=0
they separate (11.5 s vs 17.6 s).

So either the default cap should be below the default watermark gap, or the
field should be documented as a narrow-window knob. Worth settling alongside
[[ISSUE-004]], which re-measures the batching gain.
