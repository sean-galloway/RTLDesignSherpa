# math — task rollup

Math library (rtl/math, val/math, docs/markdown/rtl-math) work.

| State | Count |
|---|---|
| [active](active.md) | 0 |
| [open](open.md) | 1 |
| [closed](closed.md) | 3 |
| [dropped](dropped.md) | 0 |

## Open

- **MATH-001** — decide whether the bf16 multiplier's non-RNE rounding is
  intended or an RTL defect (interface-affecting either way).
- **MATH-002** — bf16_adder underflow can report as +infinity/overflow (wrap
  bit shared by both flags; doc promises FTZ-to-zero). Sim-settle, then
  fix RTL or doc.
- ~~MATH-004~~ closed; **MATH-001** (bf16 multiplier RNE) remains the only open math task.
