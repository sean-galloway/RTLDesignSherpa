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
