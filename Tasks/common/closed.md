<!-- Managed by the `tasks` convention: see /Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# common — Closed (done)

---

## COMMON-001 — Improve test coverage to 95%
**Status:** closed — 100% module coverage, exceeded the 95% target. P2.

Every module in `rtl/common/` has a test. Baseline coverage was ~90% with gaps
in clock utilities, synchronizers and miscellaneous modules.

## COMMON-002 — Waveform save files for all modules
**Status:** closed. P3.

GTKWave save files so a failing test opens with the relevant signals already
grouped rather than requiring them to be found by hand.

## COMMON-004 — Documentation consistency review
**Status:** closed — Phase 3 complete (all Priority 1 and 2 modules). P2.

Module documentation reconciled against the RTL: headers, parameter tables with
ranges, port lists, notes.

## COMMON-005 — Parameterization audit
**Status:** closed — audit complete. P3.

Modules scored on parameterization quality; Priority-1 modules (score < 60)
identified and addressed. See [[sizing-invariants]] for the practice this fed.

## COMMON-012 — arbiter_round_robin_simple starved agents (Kimi round_2)
**Status:** closed 2026-07-23 — RTL fixed, doc corrected, regression test now catches it

The module rotated its priority pointer the wrong direction. Rotating the
request vector LEFT by `last+1` maps rotated bit j to agent `(j - s) mod N`, so
the scan started at agent `(N - last - 1)` instead of `last + 1`. That is a
REFLECTION of the pointer, not a rotation — and a reflection composed with
itself is the identity, so the pointer oscillated between two positions. With
N=4 and all four agents requesting it granted 0,3,0,3,... forever; two of four
agents were NEVER served. Fix: rotate right first, then left back.

Measured on the real RTL under Verilator, before/after: 10/0/0/10 -> 5/5/5/5.

Three things this exposed, all now fixed:

1. **The doc table was computed for the wrong direction** and was internally
   inconsistent (its own `Selected` column could not produce its `Grant` column
   for two of five rows). Recomputed from the fixed logic.
2. **The fairness threshold was meaningless.** `min_fairness_threshold = 0.3`
   on a 4-client arbiter: Jain's index for k of n served equally is k/n, so 0.3
   passes with TWO clients completely starved (index 0.5). The test reported
   "fairness: 0.500" and PASSED against a starving arbiter. Raised to 0.7 and
   backed by a direct per-client zero-grant assertion.
3. **No stimulus ever saturated.** None of ArbiterMaster's profiles assert all
   clients continuously — even `fast` leaves a 1-3 cycle gap — so the arbiter
   was never forced to walk its rotation and the request pattern, not the
   arbiter, decided who was served. Added a `test_saturated_fairness` phase
   using the BFM's `force_client_request()` manual-control path.

Mutation-checked: the new assertion FAILS on the pre-fix RTL
("STARVATION under saturation: client(s) [0, 3] received ZERO grants") and
passes after. Full arbiter suite 23/23.

Blast radius: none in-repo. `arbiter_round_robin_simple` has no instantiators —
the sibling arbiters only name it in comments and use
`arbiter_priority_encoder` internally. It is a library module someone could
have picked up, which is exactly how it survived unnoticed.

Practice recorded in [[randomization]].
