# TASK-010: val/math: fp8 and ieee754 exponent_adder / mantissa_mult cell coverage

**Priority:** P3
**Status:** open
**Owner:** TBD

Eight cell-level FP modules have no dedicated test (found by the GTKW coverage audit, 2026-10-12):

- `math_fp8_e4m3_exponent_adder`, `math_fp8_e4m3_mantissa_mult`, `math_fp8_e5m2_exponent_adder`, `math_fp8_e5m2_mantissa_mult`
- `math_ieee754_2008_fp16_exponent_adder`, `math_ieee754_2008_fp16_mantissa_mult`, `math_ieee754_2008_fp32_exponent_adder`, `math_ieee754_2008_fp32_mantissa_mult`

They are instantiated as children of the tested adder/multiplier/fma tops, so they get indirect exercise only.

## Done when
- each cell has a directed unit test (corner exponents, denormals, round modes where applicable)
