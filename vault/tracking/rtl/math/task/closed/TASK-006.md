# TASK-006: systematic special-value Cartesian product grid for the bf16 TB family

**Priority:** P3
**Status:** FIXED 2026-10-09 (grid landed in every bf16 arithmetic TB; mutation standard met; two latent golden bugs found and fixed en route)
**Owner:** TBD

## Resolution (2026-10-09)

`bin/TBClasses/common/bf16_testing.py`:

- **`bf16_special_value_product(test_cell, *grids)`** module-level helper +
  `BF16_SPECIAL_GRID` ({+0,-0,+inf,-inf,qNaN,+submin,-submin,+1,-1}) and
  `BF16_SPECIAL_GRID_AS_FP32` (FMA accumulator expansion). Enumerates the full
  Cartesian product through the module's own `test_single_*` checker;
  one grid = unary sweep, two = 81 binary cells, three = 729 (FMA only).
  Deterministic, seed-independent, records every broken cell in one run.
- Adopted in **16 TBs**: multiplier, adder, FMA (9x9x9), comparator, divider,
  ScaleToInt8, Goldschmidt div, MaxTree (81 two-element lists), Reciprocal,
  FastReciprocal, NewtonRaphson (new special_values_test), Log2Scale, Log2
  (new), Exp2 (new), BF16ToInt. IntToBF16 skipped (integer-domain input).
  The four TBs that had no special_values_test (NewtonRaphson, Goldschmidt,
  Log2, Exp2) gained one, wired first in run_comprehensive_tests. Grid runs
  unconditionally at every test level (cheap), per the success criterion.
- **Mutation standard met**: reverting the BUG-007 divider fix turns the
  divider test RED from the directed suite alone (the 0/inf and submin/inf
  grid cells leak ow_underflow=1) -- no seed dependence. Fix restored, green.

**Latent golden bugs found by the grid (fixed in the golden, RTL unchanged,
contract now documented per the task's rule):**
- `BF16MaxTreeTB._compute_expected_max`: `all_zero` now counts subnormals as
  zero -- the RTL is explicit (`input_is_zero[i] = (exp == 0)`, with the
  comment "including subnormals treated as zero"); the golden disagreed.
- `BF16GoldschmidtDivTB._compute_expected_div`: NaN cases returned all flags
  false; the RTL drives flags independently of the result mux
  (`ow_div_by_zero = b_exp==0`, `ow_is_inf = b_exp==0 || a_is_inf`), so 0/0
  also raises div_by_zero and inf/inf also raises is_inf. Golden now encodes
  the RTL equations.

Verification: full `val/math/test_math_bf16_*.py` func suite green.

## Motivation

BUG-007 (bf16_divider, 2026-10-08) lived because `BF16DividerTB.special_values_test`
is a hand-picked list: it covered zero/finite and finite/inf but not their
zero/inf corner, and the random layer's joint probability for that cell is
~2.5e-4 per draw — found only by a lucky seed in a cocotb-version flip
matrix. BUG-004/BUG-006 are the same family: a special-value corner the
directed list never enumerated, waiting for random luck.

## Scope

- Add a shared helper in `bin/TBClasses/common/bf16_testing.py` (e.g.
  `special_value_product_test`) that enumerates the Cartesian product of the
  special classes — {+0, -0, +inf, -inf, qNaN, +subnormal-min, -subnormal-min,
  +1, -1} x itself — and runs every cell through the module's golden model.
  ~81 cells per module: trivially fast, deterministic, seed-independent.
- Adopt it in every arithmetic TB in the file (divider, multiplier, adder,
  FMA, reciprocal family, Goldschmidt, log2/exp2, clamp/max/comparator —
  wherever the golden already defines the special-case semantics).
- Cells where the golden is itself undefined (e.g. NaN payload bits) keep the
  existing loose-match convention (`bf16_is_nan` both sides).
- Where a module's contract deliberately deviates (FTZ vs gradual underflow),
  the golden already encodes it — the grid exercises the golden, so document
  the contract in the golden, not by skipping cells.

## Success criteria

- Every bf16 TB runs the full product at every level (it is cheap enough).
- Reverting the BUG-007 fix turns the divider's grid RED from the directed
  suite alone (no seed dependence) — same mutation standard as BUG-006.

## Log

**2026-10-08 -- filed** from the BUG-007 escape analysis.
