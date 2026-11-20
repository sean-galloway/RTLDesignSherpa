# TASK-003: a tighter liveness environment for the jet-prime control, and the liveness BMC run on the TASK-002 flat

**Priority:** P3
**Status:** closed 2026-11-20 (filed 2026-11-19; derived, run and closed in a morning) -- bounds 128 -> 80 from the environment's constants, liveness BMC depth 112 PASS in 1:07 on the TASK-002 flat, covers 7/7, both mutants FAIL
**Owner:** TBD

Filed 2026-11-19 at the owner's word, from the item TASK-001's stop note
named and did not file. It is the only formal residue on the fork; it
blocks nothing. TASK-001 and TASK-002 are closed on the safety prove and
the covers.

## What is unproven

The control liveness harness (`formal/jet-prime/jet_prime_control/
formal_jet_prime_control_live.sv`, `jet_prime_control_live.sby` `prove`,
BMC depth 192, boolector) holds five bounded-progress claims. On the
step-3 flat (the control before step 5) the run PASSED at depth 192 in
19:08. Since then the control changed twice -- step 5 (the single-miss
path: the launch accepted unconditionally, beats into a captured way
excluded by assumption) and TASK-002 (the 2-cycle hit) -- and the depth-192
run has not finished on either:

- step-5 flat: launched 2026-11-18 00:31, stopped by the owner at step 123
  of 192 after 15:41 (TASK-001's stop note). No counterexample through
  step 123.
- TASK-002 flat (`jet_prime_control_flat.v` 645e7cf19e, committed
  b249656e9): not run. The safety prove (depth 64) was at step 60 of 64 on
  2026-11-19 at 14:41; its verdict goes on TASK-002's closed page.

By bound, with the init sequence (about 17 steps) in front: `ap_corner`
(< 16), `ap_drain_progress` (< 24) and `ap_holdoff` (< 80) are covered by
the 123 checked steps. `ap_age0` / `ap_age1` (< 128) and
`ap_snoop_progress` (< 128) cannot fire before about step 146 on any
design, so they are unproven on both the step-5 and the TASK-002 control.
Neither change touched the age or snoop machinery; the pace is the
problem, not a suspicion.

## Why not relaunch at 192

Per-step cost grew from the step-3 flat's 19 h total to about 80 min per
step past step 110 on the step-5 flat (the environment carries more state
per unrolled step). The remaining 69 steps were about a day away when the
owner stopped it, and a day-long run that can only confirm the two
128-count bounds on machinery that did not change is the wrong spend. The
128 is slack, not a derived number: at the harness geometry (MSHR_COUNT 2,
the engine's per-slot fairness `as_done_fair*` at 24 cycles from the
accept, one commit at a time, the hold-off bound 80) an entry's worst
age is a sum of named constants, and the snoop bound likewise.

## The work

1. Derive each 128-count bound from the environment's own constants and
   write the derivation in the harness header beside the bound (the way
   the `.sby` header already derives the depth from the age bound). If
   the derived number is near 128 the environment is what has to tighten:
   bound the unconditional launch acceptance and the captured-way beat
   exclusion the step-5 flat added, the way `as_done_fair*` bounds the
   done.
2. Set the BMC depth from the new bounds (init 17 + the widest bound +
   margin, the `.sby` comment's own rule) and run `prove` on the TASK-002
   flat. Regenerate the flat first if the control moved
   (`REPO_ROOT=/tmp/rds-canonical-repo-root make -B <flat>`; the pre-commit
   check compares content).
3. Vacuity: rerun `cover` on the same flat and require 7 of 7 reached.
   A tighter assumption that prunes the waits the bounds tolerate turns a
   PASS into a proof of nothing; the handbook's formal note has the trap.
   One mutation per tightened assumption or re-derived bound (loosen the
   RTL side, see the property fail), recorded in the harness header the way
   the fabric harness records its ten.

## Done when

- `jet_prime_control_live` `prove` PASS on the current control flat at a
  depth that covers every bound with its init and setup, each bound
  derived in the header; `cover` 7 of 7 on the same flat; one mutation per
  change.
- The verdict, depth and wall time recorded on this page, on TASK-001's
  closed page (its stop note points here) and in the PRD's JP5 row.

## Not in scope

- The control safety prove (depth 64) and the fabric formal: both stand.
- Any RTL change. If the derivation exposes a real unbounded wait, that is
  a bug item, not this task.

## Progress

- 2026-11-19: filed.
- 2026-11-20: started. Step 1, the derivation (now in the harness beside
  each bound). Entry age, data-fill entry E with alloc = launch accept:
  done by age 24 (`as_done_fair`) + a snoop service in progress at the
  done, 18 (grant + 8 CD beats at <= 2 each under `as_cd_fair` + effect;
  nothing is granted later because `sn_safe_o` needs the done queue empty,
  and the commit never starts during a service) + the two entries that
  can be ahead in the done queue (FQ_DEPTH 3: the other data entry F, 7
  cycles start to next start, and the CU, 4 + beat stalls) + E's own
  commit (6 + beat stalls), with the beat stalls together <= 8 (only a
  fill accepted into F's slot after F's retire has beats left) = 67, 68
  with the done cycle. Snoop wait: the waiting snoop throttles every new
  accept (`w_sn_block_cpu` carries `sn_want_i`), so the outstanding set at
  the want is final: service 18 + the last done at 24 + three commits
  back to back with no beats left, 18 + a pended write hit's 2 = 62; a
  want under init waits <= 16 with nothing outstanding, not additive.
  Both asserted at 80 (18 % and 29 % margin) where they were 128; L4's
  hold-off keeps its 80 (the same chain from the CU's line). No
  assumption changed, so the environment is as step 5 left it; the
  derived numbers were far enough under 128 that tightening it was not
  needed. BMC depth 192 -> 112 (init 17 + 80 fires by ~98; 14 steps of
  margin; the cover depth already 112). Step 2 launched 07:00 on the
  TASK-002 flat (645e7cf19e): `prove` at depth 112 and `cover` in the
  formal dir, and two mutants in scratch copies of the flat (the real
  flat untouched): mut1 holds `C_CU_MERGE` 24 extra cycles (the age chain
  68 -> 92, past 80 and under the old 128 -- the evidence that the new
  bound has teeth and the old one had slack); mut2 drops `sn_want_i` from
  the throttle (the historical L3 counterexample: sustained misses keep
  the done queue non-empty and the snoop starves). Expected: real PASS
  around 13 h (the step-5 run's pace to step 112), mutants FAIL near step
  98. Verdicts appended when they land.
- 2026-11-20 08:07: all four runs landed. `prove` (depth 112, boolector)
  PASS at 08:07 after 1:06:45 -- against the step-5 run's 15:41 to step
  123 without finishing at the same per-step cost model; the difference
  is the bound, not the depth or the flat (same solver, same flags, same
  tool build): refuting "a counter reaches 128 in 120 steps" is a counting
  argument, which resolution handles exponentially badly, while refuting
  "an entry waits 80" is answered by the design's own retire chain. The
  prove was at step 100 after 17 min and spent most of its hour on steps
  103-112. `cover` PASS in 0:49, 7 of 7 reached (hold-off 26, corner 29,
  retire-full 31, WB wait 33, snoop wait 41, the deep ages 60 and 61).
  mut1 (`C_CU_MERGE` held 24 extra cycles, chain 68 -> 92) FAIL `ap_age0`
  at step 99 in 0:23 -- the age bound catches at 80 what 128 would have
  passed, which is the evidence the tightening has teeth and the old
  number had slack; mut2 (the throttle without `sn_want_i`) FAIL
  `ap_snoop_progress` at step 100 in 0:10, the historical L3
  counterexample reproduced. Both mutants ran on scratch copies of the
  flat; the committed flat (645e7cf19e) is untouched. Done criterion met:
  every bound derived in the header, prove PASS at a depth covering every
  bound with its init and setup, covers 7/7, a mutation per changed
  bound. Recorded on TASK-001's stop note, in the PRD's JP5 row and in
  delta 04; the lesson in the handbook's formal note. Closed.
