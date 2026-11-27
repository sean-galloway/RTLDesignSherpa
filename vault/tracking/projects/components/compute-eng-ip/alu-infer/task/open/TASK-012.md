# TASK-012: Put the multipliers and wide adders on DSP48 and carry chains

**Priority:** P2
**Status:** open -- 2026-11-26
**Owner:** sean galloway

## Why

Measured 2026-11-26 in the gatling tetrad OOC build (gatling-rv32i TASK-002): `gatling_tetrad`, four cells, alu-infer with every `ALU_EN_*` = 0 (bf16 rows, MAC, ADD, RELU, CMP), xc7a100t-1, 10 ns, routed. Vivado optimized ALU logic across the hierarchy and booked it to `u_xcell` (25,501 LUT there against 383 LUT for `gatling_xcell` built alone); grouping every LUT in `u_xcell` by the net it drives puts it back where it belongs. Per cell the ALU is about 8.7k LUT, not the 1.8k the hierarchy report shows.

The full-profile ALU (all `ALU_EN_*` = 1) is **95.6k LUT as logic for four
cells** (~24k per cell) and uses **8 DSP48E1 of 240**. The four cells do not
fit the xc7a100t (63.4k LUT).

The FP datapaths instantiate structural arithmetic from `rtl/math`:
`math_bf16_fma` uses `math_multiplier_dadda_4to2_008` and
`math_adder_han_carlson_048`; `math_ieee754_2008_fp32_fma` uses
`math_multiplier_dadda_4to2_024` and `math_adder_han_carlson_072`. A
hand-built Dadda tree cannot be mapped to a DSP48, and a Han-Carlson prefix
adder in LUTs is slower and larger than the CARRY4 chain Vivado builds from a
plain `+`. The accumulate lanes (`u_acc`, `acc_bank` next-state) are a
further 8,576 LUT for four cells in the bf16 profile.

## What

- An FPGA option for the multipliers and wide adders in the FMAs: a behavioral
  `*` / `+` (inference) under a parameter, keeping the structural trees for
  ASIC. This touches `rtl/math`, which other areas use, so the default must
  not change for them.
- Measure the full profile per cell: LUT, DSP, and how many full cells fit the
  xc7a100t and the Genesys 2.
- Pipelining (TASK-010) is separate; DSP48 mapping wants the registers TASK-010
  adds, so do the two together.

## Done when

The full profile's per-cell LUT and DSP counts are recorded in the MAS with
the option on, and four full cells either fit the xc7a100t or the MAS states
which profile does.
