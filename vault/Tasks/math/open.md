<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# math — Open

## MATH-001 — Decide: bf16 multiplier rounding is not RNE — intended or RTL defect?
**Status:** open 2026-07-29 (surfaced by math qc round_1; previously noted in dropped DOCREV-001)
**Priority:** P1 — an RTL behavior question only the owner can settle
**Owner:** Sean

`math_bf16_mantissa_mult` folds guard into sticky (`ow_sticky_bit = guard | sticky`),
so `math_bf16_multiplier` rounds on `R & (G | S | LSB)` where textbook RNE is
`G & (R | S | LSB)`. Verified truth table (LSB, guard, round, sticky): the two
agree in 10/16 patterns and disagree in 6 — five NON-tie cases (`G=0,R=1,S=1`
and `G=0,R=1,S=0,L=1` round up where RNE rounds down; `G=1,R=0,S=1` rounds down
where RNE rounds up) plus one tie (`G=1,R=0,S=0,L=1`, no round-to-even). 37.5%
of inexact guard patterns round the wrong way.

Decision needed: is the implemented boolean intentional (cheap rounding,
documented as such) or a defect? If defect: change to
`w_round_up = w_guard_bit & (w_round_bit | w_sticky_bit | w_lsb)` — but note
`mantissa_mult` currently outputs only folded (sticky|lsb) terms, so true RNE
needs the guard bit exported separately, which changes the module interface.
The docs now describe the actual behavior accurately (math qc round_1
integration, 2026-07-29); only the RTL question remains.

If intended: close with a one-line rationale and mark the doc note 'documented
behavior, not a bug'. If defect: fix RTL + the consuming modules, add a
rounding-truth-table test to val/math.
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
