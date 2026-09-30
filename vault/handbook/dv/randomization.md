---
title: Randomization
summary: FlexConfigGen's 19 named profiles are the catalogue; use backtoback to saturate. Randomized traffic alone does not prove fairness or arbitration correctness.
---

# Randomization

Three layers exist in RDS-DV and they are not interchangeable. Pick by what you
are configuring.

| Layer | Use for |
|---|---|
| `FlexConfigGen` (`shared/flex_config_gen.py`) | **Start here.** Named delay profiles, ready-made. `DEFAULT_PROFILES` is the catalogue. |
| `FlexRandomizer` (`shared/flex_randomizer.py`) | The engine underneath. Reach for it when you need a constraint shape no profile expresses. |
| `RandomizationConfig` (`shared/randomization_config.py`) | Per-field modes (CONSTRAINED / others) on packet fields, not delays. |

## The profile catalogue

19 named profiles ship in `DEFAULT_PROFILES`. The ones worth memorising:

| Profile | Shape | What it is for |
|---|---|---|
| `backtoback` | `[(0,0)]` | **Zero delay - full saturation.** The stress case. |
| `fast` | mostly 0, occasional 1-2 | near-saturation with jitter |
| `constrained` | 0 / 1-8 / 9-20 | the general-purpose default |
| `bursty` | 0 then 15-25 | clumped traffic, exercises drain paths |
| `stress` | 0-2 / 3-8 / 9-20 / 21-50 | wide spread, long tails |
| `slow`, `throttled`, `heavy_pause` | long gaps | backpressure and timeout paths |
| `chaotic`, `jittery` | irregular | hunting for timing-sensitive races |

List them at runtime rather than guessing:

    from CocoTBFramework.components.shared.flex_config_gen import DEFAULT_PROFILES
    print(list(DEFAULT_PROFILES))

## Randomized traffic does not prove fairness

This is the rule that cost real silicon-adjacent debug time.

Random profiles leave gaps. If a stimulus never asserts every requester at
once, an arbiter is never forced to walk its full rotation, and the *request
pattern* - not the arbiter - decides who gets served. A broken priority pointer
looks perfectly fair under sparse random traffic.

**Case:** `arbiter_round_robin_simple` rotated its priority pointer the wrong
direction (a reflection, not a rotation), so with all four clients requesting
it granted 0,3,0,3,... forever and starved two of four agents. Its testbench
had a fairness phase using the `default` profile, which has an
`inter_request_delay` of 5-20 cycles. All four clients were rarely up together,
the arbiter was never cornered, and the test reported a passing fairness index
for a module that starves half its clients. The bug shipped and sat in the
library.

So for any shared-resource arbiter, scheduler or picker:

1. **Saturate deliberately.** Use `backtoback`, or the BFM's manual-control path
   (`ArbiterMaster.force_client_request(c, enable=True)` for every client).
   Do not poke `dut.request` directly - the master owns that signal and will
   fight you. See [[bfm-usage]].
2. **Assert on per-client outcomes**, not on a summary index. Jain's fairness
   index for k of n clients served equally is k/n, so a "fairness > 0.3" bar on
   a 4-client arbiter passes with **two clients completely starved**. The
   `arbiter_round_robin_simple` TB had exactly that bar.
3. **Mutation-check the assertion.** Revert the fix, confirm the test goes red,
   restore. An assertion that never fails on the bug it was written for is
   decoration. Same rule as [[formal]].

## Known gaps in the framework (both closed 2026-09-27)

Both gaps below were fixed in RTLDesignSherpa-DV commit `784f905` (tooling
TASK-003). They stay recorded because the main repo's venv carries an editable
install of an OLDER framework checkout until someone runs `pip install -e` on
the DV repo again -- a session that sees the old behaviour is on the old
install, not on a regression.

- `ArbiterMaster` had its **own** private profiles (`default`, `fast`, `slow`,
  `disabled`, `manual`), none of which saturated -- even `fast` carried a 1-3
  cycle inter-request delay. Now `ArbiterMaster.catalogue_client_profiles()`
  exposes the shared `FlexConfigGen` `DEFAULT_PROFILES` (so `backtoback` is
  reachable) and a `saturate` profile holds every enabled client's request
  high. `force_client_request(c, enable=True)` remains as the per-client
  override.
- `ArbiterCompliance.analyze_round_robin_compliance()` was a **stub** returning
  `rr_efficiency: 1.0` unconditionally. It now scores the recorded grant
  history with `rr_checks` / `rr_violations` counters and reports
  `status: 'no_checks'` when it observed nothing -- a verdict needs a count
  ([[checker-verdict-needs-a-count]]). `detect_burst_behavior()` is real for
  the same reason. `check_starvation()` was always real; keep using it too.

## A per-test delay enum duplicates the catalogue

A testbench that defines its own profile enum -- `FAST_PRODUCER`,
`FAST_CONSUMER`, `MINIMAL_DELAY`, `BACKPRESSURE`, `FIXED_DELAY` -- has
re-implemented `DEFAULT_PROFILES` by hand. The catalogue already covers each of
those shapes: `backtoback` for minimal delay, `slow` / `throttled` /
`heavy_pause` for backpressure, `constrained` for the predictable middle.
RAPIDS' `DelayProfile` is the instance in this repo.

The cost is drift. A local enum stops tracking the catalogue, and a reader
cannot tell whether `MINIMAL_DELAY` means `backtoback` or something subtly
different that happens to pass today. Name a profile from `DEFAULT_PROFILES`;
if a shape genuinely is missing, add it there rather than locally.

## Randomizing two consumers TOGETHER hides every divergence bug

When a design has two parallel consumers that are supposed to stay in step,
driving both from one timing profile is not a randomized test of that
property -- it is a test of the case where they never diverge. Give each its
own draw.

*Case (2026-09-30): the RS loop harness compares a riBM decoder against a
Euclid decoder, and its host program exposed a single `throttle` that set both
checkers' ready profiles at once. Every test passed, including a dedicated
backpressure test, because equal throttles kept the two comparator FIFOs at
equal occupancy. Splitting it into `throttle_a` / `throttle_b` and drawing them
independently failed 30 of 64 runs on the first attempt, on two separate real
bugs -- a missing FIFO backpressure term and a duplicated beat. The lever that
mattered was not "more randomness" but "randomize the two things that are
supposed to track each other, separately."*

The general shape: for any invariant of the form "A and B agree", the stimulus
must be able to push A and B out of phase. Symmetric stimulus cannot.

This is one of three orthogonal axes - see [[rds-dv-axes]].

Related: [[bfm-usage]], [[seeds-and-determinism]] (a rerun that changes seeds is
not a reproduction), [[test-runner]].
