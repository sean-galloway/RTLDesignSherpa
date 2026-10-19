# TASK-008: val/math: test remaining han_carlson and dadda_4to2 widths

**Priority:** P3
**Status:** open
**Owner:** TBD

Width variants that exist in RTL but are outside their family test's parameter grid (found by the GTKW coverage audit, 2026-10-12):

- `math_adder_han_carlson_022`, `_032`, `_044`, `_072` (`rtl/math/math_adder_han_carlson_*.sv`) — test_math_adder_han_carlson.py only parameterizes 016/048
- `math_multiplier_dadda_4to2_011`, `_024` — test_math_multiplier_dadda_4to2.py only exercises 008

## Done when
- the family tests' parameter grids cover every shipped width, or dedicated per-width roots exist
