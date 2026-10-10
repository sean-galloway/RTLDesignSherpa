<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# math — bugs

**Next ID: BUG-009** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 8 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

## Closed

- **BUG-008** — math_fp8_e4m3_to_fp8_e5m2 converts the top of the e4m3 range
  (exp=15, mant=1..6; 264..448 incl. max-normal) to e5m2 NaN + ow_invalid
  (CLOSED 2026-10-10; fix-generator: narrowing conversion templates now emit the
  format-aware no-infinity source decode; module regenerated, formal prove+cover
  PASS; caught by the TASK-007 special-value grid on first landing)
- **BUG-007** — bf16_divider asserts ow_underflow on the exact-zero quotient
  0.0/inf -- CLOSED 2026-10-08 (fix-RTL): `w_result_zero` dropped its
  `~w_b_is_inf` qualifier (implied by `~w_b_eff_zero`), claiming 0/inf —
  all four signs plus FTZ subnormal/inf — for the zero-result branch, whose
  `~w_result_zero` then suppresses the flag. Directed regression added
  (5 vectors), mutation-checked; divider FULL 4/4. Escape analysis and the
  prevention task (math TASK-006, shared special-value product grid) recorded
  in the closed file.
- **BUG-006** — bf16_adder underflow can report as +infinity/overflow (wrap bit shared by both flags)
- **BUG-002** — levels are decorative: TEST_LEVEL exported but never gates depth; FULL == FUNC grids
- **BUG-003** — fp16/fp8 multiplier rounding deviates from RNE (family sweep of MATH-001)
- **BUG-004** — Multiplier underflow edge: rounding carry out of exp 0 is flushed, IEEE says min-normal
- **BUG-005** — goldschmidt_div iter2-pipe: ow_is_inf asserted on ZERO results, missed a==inf (FIXED)
- **BUG-001** — math_prefix_cell_gray.sv declared itself `math_prefix_cell` (fixed, both copies)
