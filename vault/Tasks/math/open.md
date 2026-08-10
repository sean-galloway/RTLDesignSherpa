<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# math — Open

## MATH-005 — math_mod_3_compress needs its final formal checks
**Status:** open 2026-08-08 (Sean: moved common→math and "through all reviews
except the final formal checks")
**Priority:** P2
**Owner:** TBD

`math_mod_3_compress.sv` moved from rtl/common to rtl/math (commit 3ccd1fcd,
with filelist; registry PASS, no stale doc references). Reviews are done;
the formal checks remain. No harness exists yet (nothing under formal/
matches). Write the formal harness per [[formal]] (sv2v/SBY flow,
mutation rule, vacuity traps), fold the run into the formal backlog's
coverage, and close by pointing at passing proofs.

## MATH-006 — Re-run the full math formal suite after the path repair
**Status:** open 2026-08-09 (found by the COMMON-021 formal audit)
**Priority:** P2 — every math proof result predates the rtl/math split
**Owner:** TBD

All 147 `formal/common/math_*` `.sby` configs pointed at
`../../../rtl/common/math_*.sv`, which moved to `rtl/math/` in the math
split — the entire math formal suite was unrunnable (sby dies at file-copy,
loudly, so no false passes; but every recorded PASS predates the split and
has been unverifiable since). The paths were mechanically repaired
2026-08-09 (all 147 verified resolving; see `formal/FORMAL_TODO.md`,
"Same-day follow-on finding").

Spot-verified prove+cover PASS: math_adder_brent_kung_008,
math_multiplier_dadda_tree_008, math_bf16_adder, math_fp8_e4m3_fma,
math_fp8_e5m2_fma (the fma pair also closed their prove-only rows — 5 covers
reached each). The remaining ~142 need a full re-run to reconfirm against
current RTL. Expect the 6 known BMC-intractable configs (softmax_8 x5,
bf16_exp2) to still error — that is recorded, not a regression. Consider
whether the suite should also MOVE to `formal/math/` to match the area
split, and whether `make formal-common` in CI compiles the math subset at
all today.
## MATH-007 — fp16/fp8 multiplier rounding deviates from RNE (family sweep of MATH-001)

(was drafted as MATH-006; renumbered -- the other agent's formal-suite
re-run task took MATH-006 while this was in flight)
**Status:** open 2026-08-09 (found during MATH-001's fix-every-occurrence sweep)
**Priority:** P1 — same class as MATH-001 (Sean's "fix to spec" covers these)
**Owner:** TBD

The MATH-001 pattern extends beyond bf16/fp32, with per-module variation:

- `math_ieee754_2008_fp16_multiplier.sv` / `math_fp8_e4m3_multiplier.sv` /
  `math_fp8_e5m2_multiplier.sv` all compute
  `w_round_up = w_round_bit & (w_sticky_bit | w_lsb)`.
- Their mantissa_mults export only round + TRUE sticky (no fold) and NO
  guard bit, so the decision is `R & (S | LSB)` -- not RNE, and not even the
  bf16 pre-fix form: a result strictly between half and one ulp (G=1, R=1,
  S=0, L=0) rounds DOWN when it should round up.
- Fix shape (same as bf16/fp32): export the guard from each mantissa_mult
  (fp16: guard = product[11]/[10] per norm; fp8 needs the guard computed --
  check each module's bit map), connect in the multiplier, set
  `w_round_up = w_guard_bit & (w_round_bit | w_sticky_bit | w_lsb)`.
- Verify each with the sweep harness (/tmp/csa_check/tb_rne2.sv pattern):
  DUT vs a textbook-RNE behavioral reference over several thousand pairs,
  zero mismatches; then the family suites, then mutation-check (truncate
  the guard term -> RED).
- Docs: the per-module pages' rounding claims need the same sweep after
  (the claims that bf16 round_2/3 corrected likely exist on these pages).
