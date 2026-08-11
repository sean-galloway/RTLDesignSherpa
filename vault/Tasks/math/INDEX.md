# math — task rollup

Math library (rtl/math, val/math, docs/markdown/rtl-math) work.

| State | Count |
|---|---|
| [active](active.md) | 0 |
| [open](open.md) | 2 |
| [closed](closed.md) | 7 |
| [dropped](dropped.md) | 0 |

## Recently closed

- **MATH-009** (2026-08-10) — goldschmidt_div iter2-pipe flag registers were
  swapped: ow_is_inf asserted on ZERO results and missed a==inf (values were
  right, only flags wrong). Pre-existing — exposed by the first whole-area
  FULL run since the testqc flag checks landed; fixed, 5/5 FULL on clean
  rebuild.
- **MATH-007** (2026-08-10) — fp16/fp8 multiplier RNE claim was a FALSE ALARM
  (their "round_bit" is the guard; exhaustive/directed sweep, 0 mismatches in
  all five formats). The audit still produced real fixes: 13 generated files'
  hand-fixes back-ported into the generators, the e4m3 round-carry wrap guard
  propagated to two conversions where it was live (~510 silently became +0.0),
  directed wrap stimulus added, docs and both mantissa_mult formal harnesses
  brought onto the MATH-001 contract. New finding filed as MATH-008.
- **MATH-005** (2026-08-10) — mod_3_compress formal harness written and
  passing (prove + 7/7 covers, mutation-checked).
- **MATH-001** (2026-08-10) — bf16 multiplier is textbook RNE; sweep-verified
  0/5000; suites green on clean builds.

## Open

- **MATH-006** — re-run the full math formal suite after the path repair.
  2026-08-10 run: 157/171 PASS; 6 known BMC-intractables (softmax_8 x5,
  bf16_exp2) ERROR as recorded; 2 mantissa_mult harness contract drifts found
  and fixed (now PASS); dadda_tree_016 + wallace_tree_016 (recorded PASSING
  pre-split) re-proving serially; dadda_4to2_011 / dadda_tree_032 /
  wallace_tree_csa_032 were never proven (FORMAL_PRIORITY rows say priority 0,
  "Too large").
- **MATH-008** — multiplier underflow edge: rounding carry out of exp 0 is
  flushed to zero in all five formats; IEEE post-round detection says
  min-normal. Owner decision: accept-and-document vs fix-to-spec family-wide.
