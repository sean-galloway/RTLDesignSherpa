# TASK-009: val/math: max/min/softmax_8 tree families have no tests

**Priority:** P3
**Status:** open
**Owner:** TBD

Fifteen tree/softmax modules ship in RTL with zero dedicated tests (found by the GTKW coverage audit, 2026-10-12):

- max_tree_8: `math_bf16_max_tree_8`, `math_fp16_max_tree_8`, `math_fp32_max_tree_8`, `math_fp8_e4m3_max_tree_8`, `math_fp8_e5m2_max_tree_8`
- min_tree_8: `math_bf16_min_tree_8`, `math_fp16_min_tree_8`, `math_fp32_min_tree_8`, `math_fp8_e4m3_min_tree_8`, `math_fp8_e5m2_min_tree_8`
- softmax_8: `math_bf16_softmax_8`, `math_fp16_softmax_8`, `math_fp32_softmax_8`, `math_fp8_e4m3_softmax_8`, `math_fp8_e5m2_softmax_8`

The scalar max/min ops ARE tested; only the _8 tree/softmax variants are not.

## Done when
- each family has a val/math test root (or one parametrized root per family)
