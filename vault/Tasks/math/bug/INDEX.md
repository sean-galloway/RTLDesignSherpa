<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# math — bugs

**Next ID: BUG-007** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 6 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **BUG-007** — bf16_divider asserts ow_underflow on the exact-zero quotient
  0.0/inf (`w_result_zero` misses the `a=0, b=inf` case; combinational, latent —
  surfaced by a random draw in the 2026-10-08 flip matrix; TB golden already
  expects `unf=0`). Not cocotb-version-related.

## Closed

- **BUG-006** — bf16_adder underflow can report as +infinity/overflow (wrap bit shared by both flags)
- **BUG-002** — levels are decorative: TEST_LEVEL exported but never gates depth; FULL == FUNC grids
- **BUG-003** — fp16/fp8 multiplier rounding deviates from RNE (family sweep of MATH-001)
- **BUG-004** — Multiplier underflow edge: rounding carry out of exp 0 is flushed, IEEE says min-normal
- **BUG-005** — goldschmidt_div iter2-pipe: ow_is_inf asserted on ZERO results, missed a==inf (FIXED)
- **BUG-001** — math_prefix_cell_gray.sv declared itself `math_prefix_cell` (fixed, both copies)
