<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# math — Open

## MATH-006 — Re-run the full math formal suite after the path repair
**Status:** open 2026-08-09 (found by the COMMON-021 formal audit); **re-run
executed 2026-08-10** — one heavy task still re-proving, everything else
dispositioned below.
**Priority:** P2
**Owner:** claude

All 147 `formal/common/math_*` `.sby` configs pointed at
`../../../rtl/common/math_*.sv`, which moved to `rtl/math/` in the math
split — the entire math formal suite was unrunnable (sby dies at file-copy,
loudly, so no false passes; but every recorded PASS predates the split).
Paths mechanically repaired 2026-08-09.

### 2026-08-10 full re-run (all 171 config dirs, incl. the new mod_3_compress)

| disposition | n | detail |
|---|---|---|
| PASS | 157 | prove+cover reconfirmed against current RTL |
| known BMC-intractable | 6 | softmax_8 x5, bf16_exp2 — ERROR as recorded, not regressions |
| harness contract drift, FIXED | 2 | bf16 + fp32 mantissa_mult harnesses still asserted the pre-MATH-001 folded sticky; updated to true-sticky + guard property, now PASS, mutation-checked |
| never proven (unchanged) | 3 | dadda_4to2_011, dadda_tree_032, wallace_tree_csa_032 — FORMAL_PRIORITY priority-0 rows ("Too large"/"Odd size") |
| reconfirmed serially | 1 | wallace_tree_016: low8 + boundary PASS (~35 min serial) |
| re-proving | 1 | dadda_tree_016: low8 PASS; boundary timed out at 1 h under 8-way parallelism AND at 1 h serial; 3 h serial retry in flight |

Operational notes (also in formal/FORMAL_TODO.md): `sby -f dir/cfg.sby`
resolves relative `[files]` paths against the CWD, not the .sby location —
run from inside each config dir. The 016 configs use task names
`prove_low8`/`prove_boundary`, so status-scrapers globbing `*_prove` miss
them.

Close when the dadda_tree_016 boundary retry resolves (PASS -> suite fully
dispositioned; timeout -> record it beside the priority-0 heavies with the
budget that was tried).

## MATH-008 — Multiplier underflow edge: rounding carry out of exp 0 is flushed, IEEE says min-normal
**Status:** open 2026-08-10 (found by the MATH-007 verification sweep)
**Priority:** P2 — owner decision (same intended-or-defect class MATH-001/002 started as)
**Owner:** TBD

When the pre-round exponent sum is exactly 0 (underflow by one) and mantissa
rounding carries out (product mantissa all-ones, rounds up), the true result
is exactly the minimum normal. IEEE 754 detects underflow AFTER rounding, so
the correct output is min-normal; every multiplier in the family flushes to
zero instead (asserting ow_underflow).

Measured (directed enumeration, DUT probe): fp16 364/364 cases flush, e4m3
48/48, e5m2 112/112, bf16 57/57, fp32 2,907,528/2,907,528 -- uniform across
the family, so it reads as a deliberate FTZ-at-pre-round design choice baked
into the exponent adders (underflow = pre-round es <= 0, exp_out saturates to
0). The multiplier alone cannot fix it: on underflow the exponent adder
saturates exp_out, so the "es was exactly 0" information is lost -- a fix
needs the adder to export the raw sum (or an es==0 flag) plus a multiplier
gate, across all five formats, in the GENERATORS per
[[generated-rtl-discipline]].

Decide: accept-and-document (docs/RTL headers say underflow detection is
pre-round, one boundary value flushes) or fix-to-spec family-wide. Sweep
harness pattern to verify a fix: the MATH-007 record in closed.md (exact
reference classifies these as uf_edge; uf_minnorm counter should go from 0 to
all).
