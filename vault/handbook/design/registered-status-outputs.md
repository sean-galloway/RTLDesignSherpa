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
`formal/mc_common/mc_global_timers`.

**Reviewer's tell:** a consumer that carries a comment explaining why it does
NOT trust a neighbour's status output. That comment is a bug report against the
neighbour, and it belongs there rather than as a workaround here.

Related: [[valid-ready-contracts]] (who may stall whom),
[[signal-contracts-and-kmaps]] (writing a block's published contract down at
all), [[minimal-fsm]] (one next-state function per piece of state).

## An episode stamp cannot be read in the cycle that writes it

A monitor that times an episode (a stall, a starvation) usually stamps the
time on the episode's FIRST cycle and compares `now - stamp` each cycle after.
In that first cycle the stamp register still holds the PREVIOUS episode's
time, so an age computed then is the gap since the last episode, not this
one's length -- and a one-cycle episode long after the last fires a false
timeout. Qualify the compare on an episode that already started (a cycle
counter that is nonzero, or a registered "pending" flag).
*Case (2026-10-15): `cxs_monitor_lite`'s credit timeout fired on one-cycle
starvations with a one-credit receiver (payload: 0 starved cycles, age 11 us);
only the FULL grid's CXS_MAX_CREDIT=1 cell exposed it. `axis_monitor_lite`'s
stall timeout was already guarded by `r_valid_pend`.*

## The same algebra cuts the ROOT of a cone: register the compare, not the count (2026-11-08)

The rule above is about correctness (sample the next state). The algebraic
form it recommends -- `next(c) == 0 <=> event ? (reload == 0) : (c <= 1)` --
is also the cheapest way to take a compare OFF the head of a critical cone
without changing a single cycle. memory-controllers MC-011 (granite, 100 MHz,
0.2 ns placement budget) applied it three times; the fire-cone paths it fixed
all began with 3 LUTs and ~2.5 ns of wire between a bank-timer counter flop
and the pick's fire stage, before the search had even started.

- `mc_bank_timer` (`ZF_REG`): the five zero-detects and five "within LA"
  compares, and the three auto-precharge lookahead sums, are flops fed from
  the counters' next values. With `SET_LAG` the strobes are registers, so
  every D input is register-only; the readiness outputs become one LUT from
  flops (`row_valid & z & !pending & !ap`). The pending-strobe mask stays
  OUTSIDE the flag: readiness one cycle after a fire must see the fire, and
  that term is the one place the strobe is allowed in.
- `mc_bank_queue`: `rd_valid`, `wr_ready` and `pk_valid[k]` are flags from
  the count's next value, written as the late push / pop selecting between
  compares of the registered count (`(push && !pop) ? 1 : (pop && !push) ?
  (cnt > 1) : (cnt != 0)`), never as `(cnt + push - pop) != 0`.
- `mc_bank_fifo_store`: the drain queue's `occ < DEPTH` the same way.

Each is cycle-exact and each is PROVED so: the queue against
`gaxi_age_fifo_sync` (its existing lockstep harness), the timer against a
golden copy of its live-compare form (`formal/mc_common/mc_bank_timer`,
task `equiv`). Result with the other MC-011 cuts: 179 failing endpoints
(-0.276 ns) to 0 (+0.078) under the budget on the same directive. See
[[resolve-the-select-at-the-load]] for the arbiter-cone half of that number
and [[formal]] ("golden-copy equivalence") for the proof pattern.
