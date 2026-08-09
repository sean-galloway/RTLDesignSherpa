# math — task rollup

Math library (rtl/math, val/math, docs/markdown/rtl-math) work.

| State | Count |
|---|---|
| [active](active.md) | 0 |
| [open](open.md) | 3 |
| [closed](closed.md) | 3 |
| [dropped](dropped.md) | 0 |

## Open

- **MATH-001** — decide whether the bf16 multiplier's non-RNE rounding is
  intended or an RTL defect (interface-affecting either way).
- **MATH-002** — bf16_adder underflow can report as +infinity/overflow (wrap
  bit shared by both flags; doc promises FTZ-to-zero). Sim-settle, then
  fix RTL or doc.
- **MATH-005** — mod_3_compress needs its formal harness (final gate after the
  common→math move).
- **MATH-006** — re-run the full math formal suite: all 147 math .sby configs
  were path-broken since the rtl/math split (repaired 2026-08-09, 5 modules
  spot-verified); ~142 proofs need reconfirming against current RTL.
