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

## Known gaps in the framework

- `ArbiterMaster._setup_default_profiles` defines its **own** private profiles
  (`default`, `fast`, `slow`, `disabled`, `manual`) and is not wired to
  `FlexConfigGen`. None of them saturate - even `fast` carries a 1-3 cycle
  inter-request delay. There is no `backtoback` equivalent available via
  `set_client_profile`; use `force_client_request` instead.
- `ArbiterCompliance.analyze_round_robin_compliance()` is a **stub**: it returns
  a hardcoded `rr_efficiency: 1.0` regardless of the observed grant sequence.
  It cannot detect a rotation defect. Do not treat a clean report from it as
  evidence. `check_starvation()` in the same class IS real (it reports clients
  with zero grants) - use that.

This is one of three orthogonal axes - see [[rds-dv-axes]].

Related: [[bfm-usage]], [[seeds-and-determinism]] (a rerun that changes seeds is
not a reproduction), [[test-runner]].
