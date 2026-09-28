# ISSUE-014: the documented row-hit derivation goes negative, and the board clamps it with the wrong reason

**Status:** open 2026-09-27  **Priority:** P3
**Owner:** TBD
**Found by:** TASK-015 layer 2b, on its first run against real counters.
**Related:** [[TASK-015]] (the telemetry invariants), TASK-002 (the campaign whose
explanation layer this arithmetic is).

## What was measured

`dv/tests/top/test_pumice_top.py::cocotb_test_telemetry_invariants`, board
geometry, `policy_mode=3` / `tr_init=2` (the SHIPPING reset default), three
stimulus patterns each measured as its own window at **proven quiescence** (two
consecutive identical full CSR reads), golden data on every burst:

| window | bursts | col_ops | ACT | PRE | miss | empty | ACT - col_ops |
|---|---:|---:|---:|---:|---:|---:|---:|
| `page_close_boundary` | 24 | 48 | 48 | 48 | 1 | 47 | **0** |
| `hit_miss_oscillation` | 32 | 64 | 64 | 64 | 0 | 64 | **0** |
| `bank_spread` (8 banks x 3) | 24 | 48 | **49** | 49 | 1 | 48 | **+1** |

`PAGE_STATS_MISS + PAGE_STATS_EMPTY == SCHED_STATS_ACT` held EXACTLY in all
three (1+47=48, 0+64=64, 1+48=49). That is what localises the excess: the
activation counter is not miscounting, there genuinely was one more activation
than column op.

## Why that is not a defect

Under a background-close mode a row can be opened, hit by the timeout precharge
**before its column command issues**, and then reopened -- two activations, one
column op. At `tr_init=2` that race is reachable, and the bank-spreading pattern
reaches it. The RTL is behaving correctly; it is the ARITHMETIC built on top
that is unsound.

## The actual issue

`rtl/macro/pumice_csr.rdl` documents, at the `PAGE_STATS_HIT` field:

    Row hits are DERIVED: hits = PAGE_STATS_HIT - SCHED_STATS_ACT.

That derivation returns **-1** on the run above. It is unsound for any mode that
can close a row early -- modes 2 and 3, one of which is the shipping default.

`build-perf/host/test_pumice_page_stats.py::test_hit_rate_never_goes_negative`
already clamps the result at zero, and its docstring says:

    More ACTs than column ops is physically odd but arithmetically reachable
    across a window boundary (an ACT counted whose column op landed outside).

The clamp is right. **The reason is wrong**, and that is what makes this worth
filing: the measurement above reproduces inside ONE quiescent window, so it is
not a boundary artefact, and anyone reading that docstring would go looking for
a windowing bug that is not there. A clamp with a wrong explanation is a trap --
it silently turns a real, explainable behaviour into a suppressed anomaly.

## Done when

1. The RDL field description no longer presents `col_ops - ACT` as "the"
   derivation, and says hits come from the eight `OBS_ROW_HIT[b]` counters
   (which count hits directly) with `col_ops - ACT` named as a lower bound.
2. `test_hit_rate_never_goes_negative`'s docstring names the re-activation race
   instead of a window boundary, and `PageStats.row_hit_rate` is derived from the
   per-bank counters where they are available.
3. Docs regenerated in the same pass (handbook: docs sync with configs).

Layer 2b already encodes the corrected relations -- `hits_within_col_ops` and
`hits_at_least_col_ops_minus_act`, a bound rather than an equality -- and
`dv/tests/fub/test_pumice_telemetry_invariants.py::test_act_exceeding_col_ops_is_legal_under_background_close`
pins the measured numbers so the unsound invariant cannot be reintroduced.
