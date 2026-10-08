# TASK-006: systematic special-value Cartesian product grid for the bf16 TB family

**Priority:** P3
**Status:** open
**Owner:** TBD

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
