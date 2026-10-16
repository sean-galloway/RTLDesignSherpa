# ISSUE-001: error_injector COUNT uniformity chi-square threshold trips at func depth

**Priority:** P3
**Status:** open
**Owner:** TBD
**Filed:** 2026-10-16

`dv/tests/test_error_injector.py::test_error_injector[1-8-4224-32-func]` with
SEED=33472 fails one check of 966801: `run_count_mode`'s aggregate
position-uniformity chi-square reports chi=16.42 against the TB's
`crit = 2 * n_bins` = 16.0 (`error_injector_tb.py`, end of `run_count_mode`).

The check is model-side: `all_positions` is extracted from the predicted
beats, so the result is a pure function of the seed and test level — no DUT
timing or RTL state. Confirmed pre-existing while closing BUG-001: the
identical chi=16.42 failure reproduces on the pre-fix RTL (stash + re-run,
2026-10-16).

Open questions before touching anything:

1. Is chi=16.42 a legitimate ~4%-probability tail event for this check (the
   threshold is a deliberately loose sanity bound), or evidence of mild
   position bias in the COUNT selection sampling (lhs_hi threshold scheme)?
2. If the former: loosen the threshold (e.g. 3 * n_bins), make it a warning,
   or exempt it from the assert at func depth?
3. If the latter: the bias lives in the RTL/model's COUNT placement, which
   is a real defect and should be re-filed as a bug.

## Done when

The trip is explained (tail event vs bias), and either the check is
recalibrated or a bug is filed with the mechanism.
