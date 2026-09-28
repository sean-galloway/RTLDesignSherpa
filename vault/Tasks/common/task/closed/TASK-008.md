# TASK-008: Update formal for common: staleness audit + re-prove + cover closure

> Migrated 2026-09-27 from `vault/Tasks/common/closed.md` as **COMMON-021** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-08-09 (opened and closed same day)
**Priority:** P2 — a passing proof of stale RTL is a false assurance, not a missing one

All five items done; two of them found their premise had expired, and the
audit found two problems bigger than the ones it went looking for.

1. **Staleness audit (repo-wide, force-regen + content-diff, all 48 committed
   `*_flat.v`): only 7 of 48 are content-current.** 36 stale (even 1-line
   diffs are functional — fifo_control DEPTH default drift in every rapids
   file; amba monitor files 80-220 lines behind; stream scheduler_group_array
   +2353 lines), 5 cannot regenerate (1 DEPS drift, 4 sv2v internal errors).
   Lists in formal/FORMAL_TODO.md; per-area re-prove routed there. Common's
   sole flat file is current.
2. **counter_freq_invariant was never stale.** FREQ_STRATEGY landed a week
   BEFORE the last regen; the 2026-07-25 "change" was a comment-only docs
   rename sv2v output does not carry. check-flat passes; fresh prove+cover
   PASS, covers reached. Date-based staleness diagnosis lied in BOTH
   directions across this task — only content comparison is trustworthy.
3. **Cover closure — premise expired.** All four "prove-only" modules already
   carry cover tasks. Fresh re-runs all PASS with every cover reached:
   cam_tag (2), counter (2), counter_bin (3), fifo_sync_multi_sigmap (4 —
   dir had MOVED to formal/integ_common/ in the July extraction; the
   formal/common leftovers were untracked output debris, deleted).
4. **icg cover — already fixed upstream.** Fresh cover PASS, both cover
   points reached; cp_enabled is no longer unreachable.
5. **FORMAL_TODO infrastructure corrected**: the OSS CAD Suite + sv2v are on
   the WORKSTATION at /mnt/data/tools; the "not installed" note was written
   from the laptop. The unrecorded machine split is what mis-directed the
   2026-08-08 investigation.

**Bonus finding, the biggest of the task:** the fp8 fma pair were
path-broken (rtl/common -> rtl/math), and the follow-on sweep showed ALL 147
math .sby configs broken identically — the entire math formal suite
unrunnable since the math split (loudly, at least: sby dies at file-copy).
Mechanically repaired, all refs verified resolving, five modules
spot-verified prove+cover PASS. Full re-run filed as MATH-006 (math area).

Commits: 5263bbd3 (audit + repairs + tracking), follow-up for this closure.

---
