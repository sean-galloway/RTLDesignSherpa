---
title: Measure over the window you are testing
summary: A phase-level assertion must be computed from that phase's own deltas. Scoring a phase on run-cumulative stats measures whatever ran before it - usually the phase you deliberately made unfair.
---

# Measure over the window you are testing

**A phase assertion reads deltas across that phase. Never a cumulative
counter.** If the stimulus changes between phases - and it always does, that is
what phases are for - a run-total answers a question nobody asked.

## The failure that taught it (2026-08-05)

`arbiter_round_robin`'s fairness phase counted grants correctly, as a delta
across its own window, and then scored them with a number it took from
somewhere else:

    total_new_grants = final_len - initial_len                    # windowed
    fairness_index   = final_stats.get('fairness_index', 0)       # CUMULATIVE

The phase runs last, immediately after `test_single_client_saturation`, which
grants one client almost exclusively **by design**. So the fairness check was
scored on the saturation phase. `c16_w1` failed at `0.099 < 0.25` on every run.
Computing Jain's index over the window's own per-client deltas gives **0.999**:
the arbiter was fair the whole time, and had been for as long as the check had
existed.

    window = [b - a for a, b in zip(initial_per_client, final_per_client)]
    fairness_index = sum(window)**2 / (len(window) * sum(x*x for x in window))

The same defect sat in `generate_final_report()`, gating success on
`fairness > 0.2` over the entire run. That one is not fixable by windowing -
there is no single window - so it was demoted to reporting. **A metric that
spans deliberately-unfair stimulus is not a pass criterion.**

## Why it survives review

Both halves look right in isolation. The delta arithmetic is visibly careful,
which is exactly what stops a reader from checking the line under it. Grep for
the pairing instead: a `final_x - initial_x` on one line and a `.get(...)` on
the next is the shape to distrust.

## The rule

- Snapshot **every** input to the assertion at the window start, not just the
  headline count.
- If a metric cannot be windowed, it is a log line, not an assert.
- A threshold that has to be lowered to pass - `0.3` to `0.25` here - is
  evidence the measurement is wrong, not the threshold. Fix the measurement.

Related: [[test-runner]] for level structure, [[randomization]] for the
fairness thresholds themselves, [[arbiter-compliance-model]] for the
grant-vs-request pairing the same suite got wrong.
