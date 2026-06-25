<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Test pattern: strict-flop strobe race guards

This component carries a recurring bug class: a registered output
strobe (`*_we_o`, `*_req_o`, `*_grant_o`) consumed by a downstream
FUB whose internal state lags the strobe by one or more cycles.

The canonical instance was commit `66f32c7f`
(`scheduler.sv` — `S_DONE` re-issue race). The fix landed alongside
test guards in commits `38afd10c` and `245388b3`.

This doc captures the test pattern so future req/grant or
issued-strobe additions get the same coverage on first land instead
of discovering the bug at the top level (where it manifests as
ambiguous "the read hangs sometimes" symptoms).

## When you need this test

You need a "strobe race guard" test if your FUB does any of:

- Emits a registered `*_we_o` or `*_req_o` to a downstream FUB
- Receives `*_grant_i` from an arbiter and uses it to advance an
  internal counter / FSM
- Has an internal FSM that returns to a "pick next" state in
  the same cycle as the strobe is registered

If any one is true, add a `*_no_reissue` test.

## Test template

```python
elif test_type == "<strobe>_no_reissue":
    # REGRESSION GUARD for the strict-flop strobe re-issue pattern.
    # See docs/test_patterns_strobe_race.md.
    await tb.setup(...)              # Use a configuration that
                                     # accumulates exactly ONE event
                                     # in the observation window.
    await tb.trigger_one_event()     # E.g. raise idle threshold,
                                     # accumulate one tREFI, push
                                     # one CAM slot, etc.
    # Wait for the first req/strobe.
    for _ in range(N):
        await tb.wait_clocks('mc_clk', 1)
        if tb.req():
            break
    assert tb.req()
    # Pulse grant exactly once.
    await tb.grant_one()
    # Observe for many cycles. With the bug back, the producer's
    # FSM re-picks the event and re-asserts the strobe.
    pulses = 0
    for _ in range(50):
        await tb.wait_clocks('mc_clk', 1)
        if tb.req():
            pulses += 1
        # Optional: assert internal state didn't underflow.
        assert tb.pending() <= 1
    assert pulses == 0, (
        f"{strobe}_o re-fired {pulses} times after single grant — "
        "strict-flop strobe race regressed"
    )
```

## At the macro level

Unit tests can't see the consumer's internal state lag. To catch the
full race, you also need a macro-level test that:

1. Drives the producer's input as if the consumer were there
2. After the producer fires its strobe, delays dropping the input
   by ONE mc_clk to model the consumer's register latency
3. Counts strobe pulses for one stimulus event

See `test_command_scheduler_macro.no_double_issue_race` — the model
in there is `wr_match_pending_i` dropping one cycle after
`wr_issued_we_o` asserts, simulating the CAM's `r_issued` register.
With the original scheduler bug, the producer fires `wr_issued_we_o`
twice for one stimulus; with the fix, exactly once.

## Where this guard already exists

- `dv/tests/fub/test_scheduler.py` — `no_double_issue_wr`,
  `no_double_issue_rd`, `issued_pulse_width`
- `dv/tests/fub/test_refresh_ctrl.py` — `grant_no_reissue`
- `dv/tests/fub/test_powerdown_ctrl.py` — `grant_no_reissue`
- `dv/tests/macro/test_command_scheduler_macro.py` —
  `no_double_issue_race` (full CAM-lag model)

## Where this guard is still missing

- `mode_register` — `mr_req_o` currently tied to 0 (no hot MR
  updates). Add a guard the moment that path activates.
- Any future req/grant arbitration FUB (e.g. PASR controller,
  zqcs scheduler) — add the guard on the same commit that adds
  the producer.
