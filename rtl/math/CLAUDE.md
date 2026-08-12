# Claude Code Guide: Math Library

**Purpose:** AI-specific guidance for `rtl/math/`

---

## Quick Context

**What:** 172 arithmetic modules -- integer adders/subtractors/multipliers
(Brent-Kung, Han-Carlson, Dadda, Wallace), and the floating-point families
(bf16, fp16, fp32, fp8 e4m3/e5m2: multiplier, adder, FMA, comparisons,
activations, and every cross-format conversion).
**Where the docs are:** [`docs/markdown/rtl-math/overview.md`](../../docs/markdown/rtl-math/overview.md)
-- the catalogue is [`index.md`](../../docs/markdown/rtl-math/index.md).
**Tests:** `val/math/` · **Filelists:** `rtl/math/filelists/` (lint the area
with `math_all.f`) · **Formal:** `formal/common/math_*/`

This area was split out of `rtl/common` (tests moved from
`val/common/test_math_*` to `val/math/`). A reference to
`rtl/common/math_*.sv` is stale -- fix it rather than working around it.

---

## The one rule that matters here

**Most of the FP family is GENERATED. Fix the generator, never the .sv.**
The bf16 and ieee754 families come from `bin/rtl_generators/{bf16,ieee754}/`;
a fix applied to the generated file alone is silently resurrected as a bug on
the next regeneration -- 13 files drifted that way once, three of them whole
bug classes ([[generated-rtl-discipline]] in the handbook has the case). The
audit is cheap and currently CLEAN: regenerate both families into a temp dir
and diff against the tree ignoring the `// Created:` line -- zero diffs is
the healthy state. Keep it that way: generator and regenerated .sv land in
the same commit.

---

## Rounding and underflow are settled -- do not "fix" them

- Every FP multiplier implements textbook RNE: round up iff
  `guard & (round | sticky | LSB)`, with TRUE (unfolded) sticky (MATH-001).
- The fp16/fp8 mantissa_mults export the GUARD under the name `ow_round_bit`
  and (R|S) as `ow_sticky_bit` -- a naming convention, not a bug. Their
  `round & (sticky | LSB)` IS textbook RNE. The NAMING NOTE comments in those
  files exist because this exact misreading once filed a P1 (MATH-007,
  closed false-alarm with exhaustive sweep evidence).
- Underflow is detected AFTER rounding, per IEEE 754: a rounding carry out of
  pre-round exponent 0 produces min-normal, not a flush (MATH-008, Sean's
  ruling). The adders/FMAs have NOT been audited for this corner.
- E4M3 is OCP-style: exp=0xF is normal except mant=7 (NaN); overflow
  saturates to max normal (0x7E), and rounding carry at exp=0xF must be
  caught as overflow, not wrapped (the silent-+0.0 conversion bug class).

Verification precedent for any change in this space: sweep DUT vs an
exact-integer-product reference (exhaustive for fp8), then mutation-check --
see the MATH-007/008 records in `vault/Tasks/math/closed.md`.

---

## Testing this area

- Directed patterns for functional coverage, not exhaustive sweeps --
  non-exhaustive stimulus is never a finding here (Sean).
- Every test builds from a filelist (`get_sources_from_filelist`); all 119
  tests were converted (MATH-003) -- do not reintroduce hand-listed sources.
- The TB expected-value models for the multipliers are exact integer models
  in `bin/TBClasses/common/{fp_testing,bf16_testing}.py`; float-threshold
  shortcuts were wrong at the underflow boundary three different ways.
- Run regressions via `make -C val/math clean-all && make -C val/math
  run-all-{gate,func,full}-parallel`, never bare pytest.

---

## Formal

All `formal/common/math_*` configs run against current RTL (MATH-006,
2026-08-11): 157 PASS. Known-heavy, recorded and not worth re-litigating:
softmax_8 x5 and bf16_exp2 (BMC-intractable), dadda_4to2_011 /
dadda_tree_032 / wallace_tree_csa_032 (never proven, priority 0), and
dadda_tree_016's `prove_boundary` (does not converge at 3 h serial z3;
its `prove_low8` passes). The 016 configs use task names
`prove_low8`/`prove_boundary` -- status scrapers globbing `*_prove` miss
them. `sby -f` resolves `[files]` paths against the CWD: run from inside
the config dir.

---

## Before adding a module here

1. Search first: `ls rtl/math/*.sv` -- five FP formats and a dozen adder
   families already exist; a new width of an existing family belongs in the
   GENERATOR, not as a hand-written sibling.
2. A new module lands with its `.f` in `rtl/math/filelists/` in the same
   commit, and `math_all.f` gets a line; `python3 bin/filelist_registry.py
   --check` and `--audit` must both pass.
3. Docs page under `docs/markdown/rtl-math/` (see [[module-docs]]), test in
   `val/math/` with a REG_LEVEL grid and honest TEST_LEVEL depth.
