# TASK-003: a tighter liveness environment for the jet-prime control, and the liveness BMC run on the TASK-002 flat

**Priority:** P3
**Status:** open (filed 2026-11-19)
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
