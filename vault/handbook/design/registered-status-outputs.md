# A registered status output must sample the NEXT state

**Rule:** when a block publishes a registered flag that DESCRIBES its own state
-- a readiness bit, a "window elapsed", a full/empty, a "safe to issue" -- that
flag's flop must be fed from the same next-state function the state register is
fed from. Sampling `r_state == X` into a flop publishes the state the block is
about to leave, one cycle late, and every consumer then has to compensate.

## The failure that taught it (pumice ISSUE-018, 2026-09-28)

`global_timers` tracks the JEDEC windows no single bank can see -- tFAW, tRRD,
tWTR, tRTW, tCCD -- and publishes a `*_window_ok_o` bit per window. Both the
counters and the flags were registered, and both described the same next state,
but they were derived TWICE:

```systemverilog
// the counter took the next state ...
if (evt_wr_i) r_tccd_cnt <= t_ccd_i;
else if (r_tccd_cnt > 0) r_tccd_cnt <= r_tccd_cnt - 1;

// ... while the flag took the state it was about to REPLACE
tccd_window_ok_o <= (r_tccd_cnt == 8'd0);      // WRONG
```

So the gate stayed open for exactly one cycle after the command that should have
closed it. A tCCD of 2 and a tRTW of 1 were both honoured as 1.

**Both consumers had silently grown compensation for it.**
`pumice_cmd_arbiter` stopped using `tccd_ok_i` for gating altogether ("stays an
input for observability only") and built a forward counter of its own; it added
`!(w_fire_out && r_do_rd)` terms to the turnarounds under a comment headed
"ONE-CYCLE BLIND SPOT (board round 2)", after a board ILA capture showed a tRTW
of 20 honoured as 1, four times in one 4096-sample window. tFAW and tRRD got no
compensation and were simply exposed. Nobody had written the hazard down as a
property of the block that CAUSED it -- each consumer rediscovered it on
hardware.

## The fix, and why it is structural

Compute the next state once and feed both flops from it:

```systemverilog
always_comb w_tccd_nxt = w_evt_col ? t_ccd_i
                       : ((r_tccd_cnt > 0) ? r_tccd_cnt - 1 : 0);
...
r_tccd_cnt       <= w_tccd_nxt;
tccd_window_ok_o <= w_tccd_ok_nxt;   // same next state, not r_tccd_cnt
```

That removes the CLASS, not the five instances: there is no second derivation
left to fall out of step when someone adds a sixth window.

## Do it without spending the timing you just saved

The naive form, `tccd_window_ok_o <= (w_tccd_nxt == 0)`, puts the reload mux and
an 8-bit zero-compare in series after the event strobe -- and the event strobe
comes FROM the consumer, so this is a path in a feedback loop that is usually
already critical. Use the algebraic form instead, which leaves the late signal
driving only a one-bit mux select:

```
    next(c) == 0   <=>   event ? (reload == 0) : (c <= 1)
```

Both arms compare registers or config constants, so they resolve early. Measured
on the pumice board build at 75 MHz: post-physopt WNS +0.031 after the fix
against +0.029 before, hold +0.021 against +0.016. Timing-neutral.

## How to catch it

A formal environment assumption is the natural home for this question, because
the question is exactly "is my published contract sufficient?":

    assume (!evt_rd_i || (tccd_window_ok_o && twtr_global_ok_o));

Assume ONLY what the block publishes -- no compensating term -- then assert the
real spacing against a history the wrapper keeps itself. If the proof fails, the
contract is weaker than the port list suggests. That is how ISSUE-018 was found,
and after the fix the same proof passes with the same assumptions, which is the
evidence the fix is complete. See [[formal]] and
`formal/pumice/global_timers`.

**Reviewer's tell:** a consumer that carries a comment explaining why it does
NOT trust a neighbour's status output. That comment is a bug report against the
neighbour, and it belongs there rather than as a workaround here.

Related: [[valid-ready-contracts]] (who may stall whom),
[[signal-contracts-and-kmaps]] (writing a block's published contract down at
all), [[minimal-fsm]] (one next-state function per piece of state).
