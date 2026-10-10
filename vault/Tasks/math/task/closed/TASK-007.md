# TASK-007: propagate the special-value Cartesian product grid to the IEEE-754 (fp_testing) TB family

**Priority:** P3
**Status:** FIXED 2026-10-10 (grid helper in fp_testing.py adopted by 13 base-class TBs and all 8 ieee754_2008 files; grid surfaced one real RTL bug — BUG-008 — and one clamp contract deviation now encoded in the golden)
**Owner:** TBD
**GitHub:** #95

## Resolution (2026-10-10)

`bin/TBClasses/common/fp_testing.py`:

- **`special_value_grid(fmt)`** — the nine IEEE special-value classes as
  (name, bits) pairs, generated per format: +/-0, +/-inf, qNaN, +/-min
  subnormal, +/-1. Formats without infinity (fp8 e4m3) substitute +/-max
  normal (e4m3 exp_max is finite; only mant_max is NaN), so every format
  keeps the full 9-class grid. Verified bit-exact + classifier cross-checked
  for fp32/fp16/bf16/fp8_e4m3/fp8_e5m2.
- **`fp_special_value_product(test_cell, *grids)`** — enumerates the full
  Cartesian product through the TB's own single-op checker; one grid = unary
  sweep (9), two = 81 binary cells, three = 729 ternary cells. Deterministic,
  seed-independent, records every broken cell in one run.
- Adopted in **13 base-class TBs** (runs at every test level, before the
  existing sweeps): multiplier, adder, FMA (729), comparator, max, min,
  clamp (729), ReLU, LeakyReLU, Sigmoid, Tanh, GELU, SiLU (unary), and the
  format-conversion TB (unary, source-format grid).
- Adopted in all **8 ieee754_2008 test files** via their specialized TBs
  (the SUBNORMAL_SUPPORT=1 compliant configs and divider/sqrt), through their
  *exact* `test_single_checked` checkers — closing the audit gap where the
  flagship compliant adder config had zero NaN/inf/signed-zero coverage of
  its own (its sweep only generates subnormals/normals).

## Findings surfaced by the grid (the point of the exercise)

- **BUG-008 (real RTL bug, fixed same session)**: `math_fp8_e4m3_to_fp8_e5m2`
  misclassified every finite e4m3 value with exp=15, mant=1..6 (264..448 —
  the top of the e4m3 range) as NaN, converting them to e5m2 NaN with
  ow_invalid. Generator template fix (`generate_downconvert` and
  `generate_same_size_convert` now emit the format-aware source decode that
  `generate_upconvert` already had), module regenerated, formal prove+cover
  re-run PASS. See bug/closed/BUG-008.md.
- **Clamp comparator contract (golden fix, RTL unchanged)**: the generated
  `fp_less_than` is (sign, magnitude) lexicographic and does not implement
  the IEEE -0 == +0 special case, so -0 < +0 is true in hardware. The
  FPClampTB golden now encodes that ordering (and the min-stage priority)
  exactly; the deviation is numerically invisible (±0 compare equal) and
  only observable in the min>max region, which is well-defined under the
  RTL's total ordering. All 729 cells per format now lock the full truth
  table. fp32/fp16/bf16/e5m2/e4m3 clamp were 726/729 before the golden fix;
  729/729 after.

## Verification (all in-repo, this session)

- ieee754_2008 suite: **16/16 passed** at func; every log shows the grid
  green (4x 729/729 FMA, 10x 81/81 adder/multiplier/divider, 2x 9/9 sqrt).
- val/math remainder (ieee754 files excluded): 139 passed, 6 failed on
  first grid landing (5 clamp + BUG-008's conversion); after the two fixes
  the 6 re-run **6/6 passed** — 145/145 green.
- Formal for the regenerated module: sby prove (bmc depth 2, z3) PASS, cover
  PASS.
- Note: the formal wrapper always modeled e4m3 correctly, so the buggy RTL
  still proved — no assertion covered "finite exp=15 input converts finite".
  Filed for formal hardening under BUG-008's follow-ups.

## Motivation

TASK-006 built the grid for the bf16 family and caught two latent golden
bugs plus proved the mutation standard. The ieee754_2008 suite is the
flagship compliance suite, yet its special-value coverage was inconsistent:
the compliant adder/multiplier/FMA configs ran only subnormal directed
vectors plus sweeps that never generate zero/inf/NaN, and the fp16/fp8
suites relied on an implicit `values[:20]` product that silently shifts if
the list ordering changes. One format-parameterized helper in fp_testing.py
fixes all of it at the root.

## Scope

- Helper + adoption only; no RTL changes except the BUG-008 it surfaced.
- Scope decision (Sean): ieee754_2008 files + fp_testing base classes, not
  the third "replace implicit products" option.

## Log

**2026-10-10 -- filed and fixed** after the TASK-006 closure, on "does this
make sense for ieee754 also?" — yes, per the audit, more than it did for
bf16.
