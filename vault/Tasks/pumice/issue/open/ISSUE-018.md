# ISSUE-018: global_timers publishes readiness one cycle stale, and says so nowhere

**Priority:** P2 -- the consumer compensates today, so nothing is broken on the
board; a future consumer that trusts the port list will violate JEDEC and the
symptom will be a marginal DRAM, not a failing test.
**Status:** open
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
