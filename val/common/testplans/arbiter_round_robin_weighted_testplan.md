# Test Plan: arbiter_round_robin_weighted

## Module: rtl/common/arbiter_round_robin_weighted.sv
## Test File: val/common/test_arbiter_round_robin_weighted.py
## Current Coverage: **100.0%** (Verilator line, measured 2026-08-07)

**This plan did not exist until 2026-08-07.** The module has had a test all
along -- and carried SEVEN of the 42 external test-audit findings, more than
any other module in the area -- with no plan recording what it was supposed to
check. A module whose test collateral nobody has written down is a module whose
gaps nobody can see.

## Module Overview

Credit-based weighted round-robin. Each client gets `max_thresh[i]` credits;
clients with credits are eligible for round-robin arbitration, and a global
replenish reloads all credits when no requesting client has any left.
`MAX_LEVELS_WIDTH = $clog2(MAX_LEVELS)`, so weights pack at 3 bits for
MAX_LEVELS=8 and 4 bits for 16 -- the source of a framework defect that made
client 3 decode as permanently zero-weighted (RTLDesignSherpa-DV#62).

## Scenarios

| ID | Scenario | Description | Tested | Note |
|----|----------|-------------|--------|------|
| WRR-01 | Equal weights | All clients weight 1 -> plain round robin | YES | directed, asserted |
| WRR-02 | Simple ratio | 2:1 split across two clients | YES | directed, asserted |
| WRR-03 | High dominance | One client heavily favoured | YES | directed, asserted |
| WRR-04 | Zero weights | Zero-weight client must receive NO grants | YES | exact check (`final_grants[i] == 0`) |
| WRR-05 | Geometric progression | Powers of 2, clamped to MAX_LEVELS-1 | YES | needs the counting band -- see below |
| WRR-06 | Dynamic weight change | Weights changed mid-operation | YES | windowed delta, not a cumulative counter |
| WRR-07 | Threshold operation | Behaviour across threshold settings | YES | windowed delta |
| WRR-08 | Walking requests | Each client alone in turn must be granted | YES | asserts the grant count moved (r4 finding) |
| WRR-09 | ACK mode | WAIT_GNT_ACK=1 across the grid | YES | compliance verdict asserted since 2026-08-07 |
| WRR-10 | Credit replenish | Global replenish when no requester has credit | PARTIAL | exercised, not directly asserted |

## Depth

`target_grants` scales 500/1000/2500 across gate/func/full. It was a fixed
1000 at every level until 2026-08-07, and `LEVEL_MULT` had exactly one use in
the whole TB -- so "full" was "gate" re-labelled for every checking phase.

## Distribution checking uses a counting band, not a bare tolerance

A relative-error test is meaningless for a client with a tiny expected share:
at 32 clients the geometric scenario gives client 2 ~0.9% of ~1009 grants, so
about 9 grants, where the Poisson sigma is +/-3 and a two-grant swing reads as
18.6% error. The check allows the larger of the relative tolerance or a
3-sigma band on the expected COUNT, which still catches a client that should
get ~35 grants and gets none.

## Every directed scenario must pass

There is no pass-rate tolerance. `assert pass_rate >= 0.8` over 7 scenarios
used to mean any single directed scenario could fail in every configuration
while the suite stayed green.
