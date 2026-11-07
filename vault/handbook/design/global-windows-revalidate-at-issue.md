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

## The failures that taught it: FOUR, same block, same shape

| | pumice BUG-021 | scoria BUG-001 | scoria BUG-002 | pumice BUG-033 |
|---|---|---|---|---|
| window | tRRD / tFAW | tRRD / tFAW | tZQCS | tRFC |
| checked at | STAGE-1b pre-pick | STAGE-1b pre-pick | pick cone, priority 2 | pick, live -- but the counter loads a cycle after the fire |
| fire gate re-checked it | no | no | no | yes, one cycle early |
| shown by | formal only | simulation, 3/3 seeds | formal only | board ILA, then formal (see below) |

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
its own spacing. `formal/scoria/cmd_arbiter` and `formal/mc_common/mc_cmd_arbiter`
are both ~300 lines and run in under a minute.

## The fourth: the window's first cycle belonged to the requester (pumice BUG-033, 2026-11-07)

Same block, a different seam. The arbiter's tRFC counter loads on the REF's
accepted fire (`w_fire_out && r_grant`), so in the REF's own fire cycle
`w_rfc_busy` is still 0 and `w_act_gate_live` is open. What kept an ACT out of
that cycle was the pick chain's refresh branch: while `refresh_req_i` is high
and `r_grant` is set it picks nothing. The first cycle of a rank-global window
was therefore enforced by the REQUESTER holding its request line, not by the
arbiter.

The requester has its own reasons to drop it. `mc_xddr2_refresh_ctrl` raises a
pull-in request as a function of idle (`w_idle && pullin < limit`), and
`w_idle` resets the cycle demand returns. A read that lands in the cycle the
REF is picked takes the request away in the cycle the REF fires; the demand
branch runs, the ACT is picked with the counter at zero, and it leaves one
cycle behind the REF. Board ILA (Nexys A7, 50 MHz, tRFC 7): REF, ACT bank 7
two DFI cycles later, then that bank's reads returned all-ones and all-zeros
until its next ACT -- the DRAM had dropped the activate. The token probe was
0 throughout, so the wire spacing was the arbiter's fire spacing; nothing
downstream compressed it.

Why it looked like the fast read release: the release does not touch the
arbiter, it moves when read data returns, so it moves when demand returns
relative to the idle-confirmed pull-in. The option put the traffic on the
coincidence; the hole was older than the option, and `bit off` was a small
sample, not a control.

The 2026-09-09 fix for the same two-cycle signature ("an ACT selected in the
one cycle between tRFC expiring and the next REF firing") re-checked
`w_rfc_busy` live at the pick -- the right gate, re-checking a counter that
has not loaded yet. The fix is the in-flight grant as part of the window:

```systemverilog
assign w_ref_inflight  = r_pick_valid && r_grant;
assign w_act_gate_live = !w_rfc_busy && !w_ref_inflight && tfaw_ok_i[RK0] && ...;
// and the tZQCS branch of the pick chain: w_zq_busy || (r_pick_valid && r_zq_grant)
```

Zero cost: in the normal case that cycle was already a bubble. The rule this
adds to the one above: a global window is OWNED by the fire gate from the
cycle its command fires, not from the cycle its counter loads. If the counter
loads on the fire, the granted command sitting in the output register is the
window's first cycle, and no request line from another block may be what
closes that seam.

How it was pinned: `formal/mc_common/mc_cmd_arbiter` had tRRD/tFAW assertions
and no tRFC one. A tRFC assertion in the same shape (the wrapper times REF to
ACT itself, `refresh_req_i` free) fails at step 6 on the pre-fix RTL with
exactly the board trace -- grant with the request already low, ACT the next
cycle, counter loading as it fires -- and passes to depth 30 with the fix. The
char-harness sim could run the board's profile against the DFI-wire scoreboard
(`CMD_HISTORY_EN=1 HIST_T_RFC_CORE=3`) for the same question; the proof
answered it in thirty seconds and named the cycle.

See also [[registered-status-outputs]] (the producer-side twin: a registered
readiness flag that samples the state it is leaving) and
[[priority-logic-depth]] (why these gates are kept shallow, which is the
pressure that put the check upstream in the first place).
