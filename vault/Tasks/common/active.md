<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# common — Active (in progress)

---

## COMMON-021 — Update formal for common: staleness audit + re-prove + cover closure
**Status:** active 2026-08-09 — items 1-5 all effectively done same day; only
the fifo_sync_multi_sigmap fresh re-run is still in flight (close when it
lands PASS)
**Priority:** P2 — a passing proof of stale RTL is a false assurance, not a missing one

**Progress 2026-08-09 (workstation — which HAS the toolchain; the laptop
note was about the laptop):**
- Item 1 DONE: repo-wide audit ran (force-regen + content-diff, all 48
  committed flat files). Only 7 of 48 are current; 36 stale, 5 cannot regen.
  Full results in `formal/FORMAL_TODO.md` ("Flat-file staleness audit
  results"). Common's sole flat file (counter_freq_invariant) is CURRENT.
- Item 2 DONE: counter_freq_invariant was never stale — `FREQ_STRATEGY`
  landed a week BEFORE the last regen, and the 2026-07-25 "change" was a
  comment-only docs-path rename that sv2v output does not carry. check-flat
  passes; prove + cover re-run PASS, cover points reached.
- Item 5 DONE: FORMAL_TODO Infrastructure section now records the
  workstation/laptop split.
- Non-common staleness (amba/stream/rapids/converters) routed to
  FORMAL_TODO per-area follow-up, not this task.
- Item 3 DONE (premise expired): all four "prove-only" modules already carry
  cover tasks. cam_tag/counter/counter_bin re-run fresh: prove+cover PASS,
  all covers reached, zero unreached. fifo_sync_multi_sigmap's dir MOVED to
  formal/integ_common/ (July extraction); its fresh re-run is the one still
  in flight. Leftover output debris under formal/common/fifo_sync_multi{,_sigmap}
  deleted.
- Item 4 DONE (also already fixed upstream): icg fresh cover PASS, both
  cover points reached — cp_enabled is no longer unreachable.
- Bonus: the fp8 fma pair were path-broken (rtl/common -> rtl/math);
  fixed, prove+cover PASS, 5 covers reached each. The follow-on sweep found
  ALL 147 math .sby configs broken the same way — repaired + spot-verified,
  full re-run filed as MATH-006 (math area).

The common-area formal collateral (`formal/common/`, ~58 non-math + ~175 math
`.sby` configs) needs bringing back to a trustworthy state. Full context in
`formal/FORMAL_TODO.md` ("Run list for a machine WITH the toolchain",
2026-08-08). The pieces, in order:

1. **Staleness audit of every checked-in `*_flat.v`.**
   `counter_freq_invariant_flat.v` was found 3 months out of date by accident
   (RTL changed 2026-07-25, flat file frozen 2026-04-17) — every proof run in
   between validated RTL that no longer existed, silently, because the flat
   files are committed and `git checkout` makes mtime useless. The
   `check-flat` content-diff target in
   `formal/common/counter_freq_invariant/Makefile` is the pattern; roll it out
   to every sv2v-based harness and ideally CI.
2. **Regenerate and re-prove counter_freq_invariant** against the current RTL
   (it gained `FREQ_STRATEGY` + a `pow2_freq` function since the flat file was
   made). A post-regeneration failure is a REAL design result, not tooling.
3. **Close out the prove-only common modules** — cam_tag, counter, counter_bin,
   fifo_sync_multi_sigmap (+ math fp8 fma x2) pass prove but have no cover
   task, so nothing shows the properties are non-vacuous.
4. **Fix the icg cover failure** (cp_enabled unreachable — latch gate timing;
   needs deeper cover or relaxed assumptions).
5. **Correct `formal/FORMAL_TODO.md`'s Infrastructure section** to record WHICH
   machine has the OSS CAD Suite — the stale location claim is what
   mis-directed the 2026-08-08 investigation.

Toolchain gate: needs a machine with sv2v + yosys + sby (`source env_python`
first). The 2026-08-08 note records the laptop does NOT have them.
