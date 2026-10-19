# TASK-005: IEEE 754 gradual underflow (SUBNORMAL_SUPPORT) across the ieee754 family + new fp32 divider and sqrt (math)

**Priority:** P2. Feature work from intent, not a defect — the legacy FTZ
datapath is the default and is untouched at `SUBNORMAL_SUPPORT=0`.
**Status:** CLOSED 2026-10-07 — landed as five commits on main (unpushed at
filing time), each carrying its generator change, regenerated `.sv`, filelist,
and an exact-integer-oracle val suite. Docs updated the same day
(`docs/markdown/rtl-math/math_ieee754_modules.md` rewritten — its old overview
overclaimed "full IEEE compliance" while the RTL was FTZ; `index.md`,
`overview.md`, `math_library.md` catalogues bumped; `rtl/math/CLAUDE.md`
updated, including retiring its "adders/FMAs unaudited for the BUG-004 corner"
line). No formal configs added — verification is val-only, matching the area's
posture for these blocks.

**Scope:** `rtl/math/math_ieee754_2008_*` fp16/fp32 arithmetic (adder,
multiplier, FMA) plus two new iterative fp32 units; generators under
`bin/rtl_generators/ieee754/`; suites in `val/math/`.

## Commits (all on main, in landing order)

1. `cf9520e2b` — SUBNORMAL_SUPPORT on the fp32/fp16 adders: subnormal
   operands decode hidden-0 at effective biased exponent 1 (fp32
   equal-exponent swap tiebreak now compares `{hidden, mant}` so a subnormal
   can never win the swap its hidden-0 significand would break; fp16 absorbs
   an inverted pick via its sum-negative detect, as it always has); subnormal
   sums right-shift onto the grid with sticky capture, rounded RNE; at =1 a
   negative adjusted exponent no longer feeds the legacy
   saturation-to-infinity corner that =0 keeps bit-for-bit (its low byte can
   read as 0xFF).
2. `0dc286dbd` — SUBNORMAL_SUPPORT on the fp32/fp16 multipliers: fp32 feeds
   hidden-bit + adjusted exponent straight into the shared mantissa_mult; the
   fp16 mantissa_mult zeroes a subnormal operand outright, so fp16 takes the
   decoded-significand product from a parallel 11x11 Dadda that fires only
   when =1 sees a subnormal (=0 datapath untouched); sub-1.0 products
   left-normalize into [1,2) with an exponent debit; subnormal-grid results
   carry TRUE unfolded sticky (math ISSUE-001).
3. `f0b5e3f3f` — SUBNORMAL_SUPPORT on the fp32/fp16 FMAs:
   pre-normalize-by-placing — the raw Dadda product enters the accumulator
   frame at its TRUE (unnormalized) position, bit-exact equivalent to the
   legacy needs_norm placement for all-normal operands, so the alignment
   shift range is unchanged; TRUE sticky through the alignment shift, with
   `w_dropped_tie` pinning the align-sticky-only subtract tie DOWN (the naive
   sticky-OR tie-break rounds up; the dropped bits make the exact sum
   smaller); single-rounded fused semantics preserved.
4. `065148c0a` — NEW `math_ieee754_2008_fp32_divider` (RISC-V FDIV.S class):
   Goldschmidt multiplicative divide; 7-bit-index/12-bit-entry reciprocal
   seed LUT (|r0*b - 1| <= 2^-7.96 at every bucket end) + two Newton
   refinements on the shared fp32 mantissa_mult; residual-based faithful RNE
   correction. Root-cause fix en route: every Newton operand now presents its
   own bit 23 — a phantom hidden bit had corrupted the second refinement in
   the top LUT buckets (+0x40-ulp quotient errors). Latency 1/9/10.
5. `02140c782` — NEW `math_ieee754_2008_fp32_sqrt` (RISC-V FSQRT.S class):
   Newton-Raphson reciprocal-sqrt; 7-bit-index/12-bit bucket-center seed LUT
   targeting r* = 2^23*sqrt(2/b); two refinements of e = 3/2 - b*r^2/2
   (exhaustively bounded over all 2^24 significands at generate time);
   y = S*r2 with odd/even exponent handling; EXACT residual rounding via an
   incremental-square isqrt chain — W is an integer and (k+1/2)^2 is not, so
   half-ULP ties can never occur and RNE degenerates to exact
   round-to-nearest. Latency 1/10/11.

## SUBNORMAL_SUPPORT semantics (all eight arithmetic blocks)

`parameter bit SUBNORMAL_SUPPORT = 1'b0` on every block: fp16/fp32 adder,
multiplier, FMA, fp32 divider, fp32 sqrt.

- **=0 (default)** — legacy FTZ, byte-identical to the pre-change RTL.
  Subnormal operands are effective zeros; a nonzero subnormal-range result
  flushes to signed zero AND asserts `ow_underflow` (at =0 the flag marks
  the flush).
- **=1** — full IEEE 754-2008 gradual underflow, inputs and outputs.
  Subnormal operands decode with hidden bit 0 at effective biased exponent 1;
  results round RNE onto the subnormal grid. Underflow is detected AFTER
  rounding — tiny AND inexact (math BUG-004 ruling) — and a rounding carry
  out of pre-round exponent 0 yields min-normal, never a flush.
- NaN / infinity / zero special cases are identical in both modes; only
  subnormal handling changes.
- The adders never assert `ow_underflow` for a subnormal sum (the exact sum
  of two grid points is itself a grid point the subnormal encoding holds);
  the multiplier, FMA, and divider can assert it (their subnormal-boundary
  results round inexact).
- **Sqrt cannot underflow or overflow** — halved exponents move every
  magnitude toward 1 — so it has no `ow_overflow` port and `ow_underflow` is
  tied `1'b0`; =1 only left-normalizes subnormal INPUTS with an exponent
  debit. A sqrt result is never subnormal. FTZ folds a positive subnormal
  sqrt input into +0 with no invalid.
- **FTZ flag quirk (=0):** effective-zero folding makes `subnormal * inf`
  raise **qNaN + invalid** at =0 but return **inf** at =1 (where the
  subnormal is a real operand and only `0 * inf` is invalid).

## Measured latencies (TB-pinned per class, accept edge -> ow_valid)

| Unit | Special | Normal path | Subnormal-related |
|------|---------|-------------|-------------------|
| fp32 divider | 1 cycle | 9 cycles | 10 cycles when the exact quotient lands on the subnormal grid (=1 only; the S_SUBN compare cycle) |
| fp32 sqrt | 1 cycle | 10 cycles (odd input exponent) | 11 cycles (even; the extra 1/sqrt(2) significand-scale cycle) |

Multipliers/FMAs are combinational; adders take 0-4 stages from
`PIPE_STAGE_1..4`.

## Durable quirks (for the next consumer)

- The fp32 and fp16 `mantissa_mult` spend `i_*_is_normal` differently: fp32's
  port **is the hidden bit** (`{i_a_is_normal, i_mant}` — pass 0 to multiply
  a subnormal significand); fp16's **selects 1.mant vs 0.0** and zeroes the
  operand outright, so it can never produce a subnormal product.
- That hidden-bit contract is the integration contract for any future
  consumer of the shared fp32 unit (multiplier, divider, and sqrt all feed it
  this way): every FSM operand must present its own bit 23. The divider slice
  shipped exactly that bug — a phantom hidden bit in the second Newton
  refinement, fixed +0x40-ulp quotient errors in the top LUT buckets.

## Verification basis (all five commits)

Exact-integer oracles throughout (u = 2^(1-bias-mant_bits) integer grid; no
floats in the expected-value path), per-vector checks of result bits plus
`ow_overflow`/`ow_underflow`/`ow_invalid`, both SUBNORMAL_SUPPORT values at
every REG_LEVEL; legacy float-oracle TBs skip themselves on =1 builds. Adder
oracle cross-validated against an independent `fractions.Fraction` model on
30k subnormal-heavy samples per format, 0 mismatches. Divider
gate/func/full: sn0 396/528, 972/1296, 3276/4368; sn1 411/548, 987/1316,
3291/4388 (0 failed). Sqrt gate/func/full: sn0 222/333, 606/909, 2142/3213;
sn1 234/351, 618/927, 2154/3231 (0 failed; 1071 vectors per param at full).
Generator zero-drift regen clean for the family. `filelist_registry
--check/--audit/--placement` PASS; verilator -Wall and lint-decl-order PASS.
The docs slice is verified by review against these same RTL facts, not by
re-simulation.
