# A global timing window must be re-validated at the issue stage

**Rule:** if a timing window is NOT a per-bank (per-resource) property -- tRRD,
tFAW and tZQCS on a DRAM controller; any device- or rank-global obligation --
then checking it where the command is SELECTED is not enough. It must be
re-checked in the gate that lets the command FIRE. Every pipeline stage between
the two is a cycle in which the window can close under a command already
committed to issue.

The per-resource windows are safe to check once, because the resource's own
timer travels with the command. A global window has no such owner, so nothing
downstream notices it went stale.

## The failures that taught it: THREE, same block, same shape

| | pumice BUG-021 | scoria BUG-001 | scoria BUG-002 |
|---|---|---|---|
| window | tRRD / tFAW | tRRD / tFAW | tZQCS |
| checked at | STAGE-1b pre-pick | STAGE-1b pre-pick | pick cone, priority 2 |
| fire gate re-checked it | no | no | no |
| shown by | formal only | simulation, 3/3 seeds | formal only |

All three are one error written three times, and the first two are the same
block in two controllers -- pumice's arbiter and the scoria port of it. The
third was found by the formal proof written to close the second, within minutes
of it first running.

### Why the local checks all looked sufficient

Each had a plausible-looking guard that could not possibly see the problem:

- **the per-bank timers** (`bank_timer`) enforce tRCD, tRP, tRAS. They are
  per-bank by construction, so a cross-bank tRRD is invisible to them.
- **the command-history checker** is same-bank by design. It audits the
  command stream and still cannot see two ACTs to DIFFERENT banks landing a
  cycle apart.
- **the pick cone's own block** (`else if (w_zq_busy)`) looks like exactly the
  right check -- and is, one cycle too late, because the window counter loads
  on the ACCEPTED FIRE. During the ZQCS's own fire cycle the counter is still
  zero.

So the gap is structural, not an oversight anyone would spot by reading the
guard: every guard present was correct about something that was not the
question.

### The tell in the comments

scoria's tZQCS counter carried this, written by the author as a design note:

> a refresh is kept out of the tZQCS window by the cone's priority-2 block,
> not by a term on `w_ref_safe`

That sentence IS the bug report. Priority-2 is the check that is one cycle
late. When a comment explains that a global obligation is enforced somewhere
other than the final gate, read it as a finding rather than as documentation.

## The fix shape, and why rejecting late is safe

```systemverilog
if      (r_do_act)            w_out_safe = bank_act_ready_i[RK0][r_bank]
                                        && tfaw_ok_i[RK0] && trrd_ok_i[RK0]
                                        && !w_zq_busy;
```

One AND term per global window, on the gate that already qualifies the fire.
Dropping a command this late is lossless given two properties that must be
checked before relying on it:

1. **every downstream commit is qualified by the fire signal**, so an unfired
   entry stays schedulable and is simply re-picked. (On scoria: `w_out_reject`
   returns the slot to the CAM, and every CAM commit/issue is gated on
   `w_fire_out`.)
2. **the windows are countdowns**, so a persistently closed gate cannot
   livelock -- it opens on its own.

Throughput cost measured on scoria BUG-001: 42 ACTs in a window before the fix,
43 after. Re-picking costs a cycle or two, not a cliff.

## Sim will not find these, and that is predictable

pumice BUG-021 and scoria BUG-002 were formal-only; scoria BUG-002 failed to
reproduce in 0 of 10 simulation alignments even when the mechanism was known
and the stimulus written for it. The reason is the pick pipeline: 3-4 stages,
and the violating trace needs a command already in flight at the one cycle the
window flips. Random traffic finds that rarely, and a hand-written case has to
guess the alignment.

What DOES find them, cheaply: compose the gating block with the gated block --
the real one, not a model -- let the environment free, and time the events with
a counter the wrapper keeps itself rather than trusting either DUT to report
its own spacing. `formal/scoria/cmd_arbiter` and `formal/pumice/cmd_arbiter`
are both ~300 lines and run in under a minute.

See also [[registered-status-outputs]] (the producer-side twin: a registered
readiness flag that samples the state it is leaving) and
[[priority-logic-depth]] (why these gates are kept shallow, which is the
pressure that put the check upstream in the first place).
