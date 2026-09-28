# ISSUE-018: global_timers publishes readiness one cycle stale, and says so nowhere

**Priority:** P2 -- the consumer compensates today, so nothing is broken on the
board; a future consumer that trusts the port list will violate JEDEC and the
symptom will be a marginal DRAM, not a failing test.
**Status:** CLOSED 2026-09-28 (resolution below)
**Owner:** TBD
**Found by:** `formal/pumice/global_timers` -- the proof was written to ask "if
the scheduler issues only when this block says it may, is JEDEC satisfied?" and
the answer came back NO in four steps.
**Related:** [[project_pumice_mask_ap_hazard_and_tccd_csr]] (the board's tCCD CSR
left unprogrammed -- the same signal, a different way to not enforce it)

## The seam

Every readiness output of `global_timers` is strict-flopped, and the counter it
reports is reloaded on the same edge as the command that should close the gate.
So the gate stays open for exactly one cycle after that command. The engine's
counterexample, with `t_ccd_i=2` and `t_rtw_i=1`:

| cycle | event | `tccd_window_ok_o` | `trtw_window_ok_o` |
|---|---|---:|---:|
| 2 | `evt_rd_i=1` -- reloads tCCD=2, tRTW=1 on the edge | 1 | 1 |
| 3 | **`evt_wr_i=1` permitted** -- one cycle after the read | 1 | 1 |
| 4 | the flags finally drop | 0 | 0 |

At cycle 3 the wrapper's own history has `age_col=0` against `t_ccd=2` and
`age_rd=0` against `t_rtw=1`. Both violated, both permitted by the block.

This is not specific to tCCD/tRTW. tFAW, tRRD and tWTR are the same structure:
counter reloaded on the event, readiness flopped from the pre-reload value.

## Why nothing is broken right now

`pumice_cmd_arbiter` already compensates, in two different ways, and its
comments describe the hazard precisely -- it just never got written down as a
property of the block that causes it.

For tCCD the arbiter does not use the signal at all:

> `tccd_ok_i` is a flop that reloads on the column FIRE, 3 pipeline cycles after
> the column was classified [...] This REPLACES the flopped global `tccd_ok_i`
> on the column masks [...] **`tccd_ok_i` stays an input for observability
> only.**

For the turnarounds it adds its own term, under a heading that names this exact
bug:

> **ONE-CYCLE BLIND SPOT (board round 2).** [...] a WRITE picked in the very
> cycle a READ fires out sees `r_rdfire0` still 0 and issues one cycle behind it
> -- exactly the surviving `RD@2027 -> WR@2028 gap=1`.

That one was found on a board ILA capture: a tRTW of 20 honoured as 1, four
times in a single 4096-sample window.

## What is actually open

Three things, and they are separable:

1. **The contract is undocumented.** `global_timers.sv`'s header describes what
   each timer tracks and says nothing about the outputs being a one-cycle-stale
   view that a consumer must supplement. Every consumer so far learned it from
   a board failure. The cheapest fix by far: say so at the port declarations.

2. **tFAW and tRRD have no compensating term.** The arbiter's ACT gate is
   `w_act_gate_live = !w_rfc_busy && tfaw_ok_i[RK0] && trrd_ok_i[RK0]` -- the
   flags directly, with nothing like the `!(w_fire_out && r_do_rd)` term the
   turnarounds got. Two ACTs to DIFFERENT banks in consecutive cycles are not
   stopped by `bank_timer` either, since its windows are per-bank and tRRD
   exists precisely to cover the cross-bank case. **Whether the full pick
   pipeline can actually present two ACTs one cycle apart is NOT established
   here** -- proving it needs the arbiter in the cone, which is a much larger
   proof than this one. It may well be unreachable for an unrelated reason. That
   is the open question.

3. **Or move the staleness out of the block.** Reporting `(counter == 0)`
   combinationally, or reporting `counter <= 1` from the flop, would make the
   published flag mean what a reader assumes. Both cost timing on a block whose
   outputs feed the arbiter's critical cone, which is why the flop is there --
   so this is a trade, not an obvious win, and it is Sean's call.

`formal/pumice/global_timers` currently proves the spacing under the contract
the arbiter actually implements (published flag PLUS one cycle of the
consumer's own), and its assumption block carries the counterexample above.
That is honest but it is also the weaker statement: the proof cannot say this
block alone is sufficient, because it is not.

---

## Fixed 2026-09-28 -- one next-state function instead of two derivations

The seam had a single structural cause, and the fix removes the class rather than
the instances.

The readiness outputs and the counters are BOTH registered, and both are
descriptions of the same next state -- but they were derived twice. The counter
flop sampled the next-state value; the readiness flop sampled `r_*_cnt == 0`,
i.e. the state it was about to replace. So the readiness flop was always
describing the previous cycle's counters.

`global_timers` now computes the next state ONCE (`w_faw_nxt`, `w_trrd_nxt`,
`w_twtr_nxt`, `w_trtw_nxt`, `w_tccd_nxt`) and feeds both the counter flops and
the readiness flops from it. There is no second derivation left to fall out of
step.

### The proof obligation, and it is the whole point

`formal/pumice/global_timers` asked "if the scheduler issues only when this block
says it may, is JEDEC satisfied?" -- and the answer was NO, which is why this
issue exists. Its environment now assumes **only what the block publishes, with
no compensating term**:

    assume (!evt_act_i || (tfaw_window_ok_o[0] && trrd_window_ok_o[0]));
    assume (!evt_rd_i  || (tccd_window_ok_o && twtr_global_ok_o));
    assume (!evt_wr_i  || (tccd_window_ok_o && trtw_window_ok_o));

and all five JEDEC windows hold. Reverting only the two readiness assignments
brings the bug straight back (`a_tccd` and `a_twtr` fail), so the proof is
checking the fix and not something adjacent.

### Item 2 of "what is actually open" is answered, not merely mitigated

The open question was whether tFAW/tRRD -- which had no compensating term
anywhere -- were exposed. That question no longer needs answering: the fix is in
the block, so tFAW and tRRD are correct at the source without the consumer
needing a term at all. Establishing whether the arbiter's pick pipeline could
*reach* the two-ACTs-one-cycle-apart case is now moot.

### Written on timing, deliberately

Each readiness expression is arranged so the LATE signal -- `evt_*`, from the
arbiter's command output -- drives only a one-bit mux select, with both arms
comparisons of registers or CSR constants that resolve early:

    next(c) == 0   <=>   event ? (reload == 0) : (c <= 1)

Testing `w_*_nxt == 0` directly would instead put the reload mux and an 8-bit
zero-compare in series after `evt_*`, on a path feeding back into the arbiter's
own critical cone, on a design whose board WNS is deliberately thin.

### What this does NOT change

* **The arbiter's compensating terms stay.** Its tCCD forward counter and the
  `!(w_fire_out && r_do_rd)` turnaround terms are now redundant with respect to
  this hazard, but they also cover a SEPARATE one -- the ~3-cycle pick-pipeline
  latency between classify and fire, which is not this bug and is not fixed by
  this change. Removing them is a different piece of work with its own board
  evidence requirement.
* **The loaded-counter convention.** A window programmed to N is enforced as N+1
  cycles of spacing (the counter is loaded with N and the gate opens when it
  would reach 0). That is one cycle conservative, unchanged by this fix, and
  changing it moves measured bandwidth -- a separate decision.
* `obs_*` and the readiness outputs are now aligned in the SAME cycle rather than
  one apart. Nothing consumes `obs_*` today (every one is left unconnected at the
  `pumice_mem_cmd_scheduler` instantiation), so this breaks no reader.

### Gates, all green

| Gate | Result |
|---|---:|
| pumice regression (`clean-all` then `run-all-full-parallel`) | 175 fub / 171 macro / 518 top / 48 phy + 6 skipped, rc 0 |
| char-framework sim (the board gate) | 216 passed, 2 xfailed, rc 0 |
| `formal/pumice` (4 modules, 9 sby tasks) | 9/9 PASS |
| 75 MHz bitstream, post-physopt | WNS **+0.031**, WHS **+0.021**, TNS/THS 0 |

Every count matches the pre-change baseline, and the bitstream's WNS is
marginally BETTER than the +0.029 / +0.016 it replaced -- which is what writing
each readiness expression as a one-bit mux select on the late signal was for. A
thin positive WNS is this design's deliberate operating point, so "unchanged" is
the result to want here, not a number to celebrate.

Docs synced in the same pass: `pumice_mas/ch02_blocks/19_global_timers.md`
(the contract, the tFAW wording, the obs alignment), `10_xbank_timers.md` (which
stated `trrd_window_ok_o[r]` IS `(r_trrd_cnt[r] == 0)` -- the old form, now
wrong), `pumice_has/ch03_architecture/03_bank_machines.md`, and
`uarch/PUMICE_MEM_CMD_SCHEDULER_UARCH.md` (why the arbiter's extra guards are
still needed for the pick-pipeline hazard, which this fix does not address).
