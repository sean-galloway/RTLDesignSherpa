# Master filelist for the math library (rtl/math).
# Location: rtl/math/filelists/math_all.f
#
# Split out of rtl/common in the AMBA/common/math reorg: math_* modules are
# a self-contained arithmetic library (adders, multipliers, float formats)
# with no dependency back on rtl/common. Consumers -f this file, or the
# individual per-module filelists alongside it.

# Blocks from rtl/common that math modules instantiate. They stayed in common
# in the arithmetic split (they serve more than arithmetic), so math is a
# CONSUMER of them and -f includes the owner's list rather than hand-listing.
# Without these, seven modules -- the bf16/fp16/fp32 adders and FMAs, and
# math_int_to_bf16 -- fail to elaborate with "Cannot find file containing
# module: count_leading_zeros". Nothing caught it because rtl/math had no
# Makefile until 2026-07-26, so the area was never linted.
-f $REPO_ROOT/rtl/common/filelists/count_leading_zeros.f
-f $REPO_ROOT/rtl/common/filelists/shifter_barrel.f

-f $REPO_ROOT/rtl/math/filelists/math_adder_brent_kung_008.f
-f $REPO_ROOT/rtl/math/filelists/math_adder_brent_kung_016.f
-f $REPO_ROOT/rtl/math/filelists/math_adder_brent_kung_032.f
-f $REPO_ROOT/rtl/math/filelists/math_adder_brent_kung_064.f
-f $REPO_ROOT/rtl/math/filelists/math_adder_brent_kung_bitwisepg.f
-f $REPO_ROOT/rtl/math/filelists/math_adder_brent_kung_black.f
-f $REPO_ROOT/rtl/math/filelists/math_adder_brent_kung_gray.f
-f $REPO_ROOT/rtl/math/filelists/math_adder_brent_kung_grouppg_008.f
-f $REPO_ROOT/rtl/math/filelists/math_adder_brent_kung_grouppg_016.f
-f $REPO_ROOT/rtl/math/filelists/math_adder_brent_kung_grouppg_032.f
-f $REPO_ROOT/rtl/math/filelists/math_adder_brent_kung_grouppg_064.f
-f $REPO_ROOT/rtl/math/filelists/math_adder_brent_kung_pg.f
-f $REPO_ROOT/rtl/math/filelists/math_adder_brent_kung_sum.f
-f $REPO_ROOT/rtl/math/filelists/math_adder_carry_save.f
-f $REPO_ROOT/rtl/math/filelists/math_adder_carry_save_nbit.f
-f $REPO_ROOT/rtl/math/filelists/math_adder_full.f
-f $REPO_ROOT/rtl/math/filelists/math_adder_full_nbit.f
-f $REPO_ROOT/rtl/math/filelists/math_adder_half.f
-f $REPO_ROOT/rtl/math/filelists/math_adder_pg_chain.f
-f $REPO_ROOT/rtl/math/filelists/math_adder_ripple_carry.f
-f $REPO_ROOT/rtl/math/filelists/math_addsub_full_nbit.f
-f $REPO_ROOT/rtl/math/filelists/math_multiplier_basic_cell.f
-f $REPO_ROOT/rtl/math/filelists/math_multiplier_carry_save.f
-f $REPO_ROOT/rtl/math/filelists/math_multiplier_dadda_tree_008.f
-f $REPO_ROOT/rtl/math/filelists/math_multiplier_dadda_tree_016.f
-f $REPO_ROOT/rtl/math/filelists/math_multiplier_dadda_tree_032.f
-f $REPO_ROOT/rtl/math/filelists/math_multiplier_wallace_tree_008.f
-f $REPO_ROOT/rtl/math/filelists/math_multiplier_wallace_tree_016.f
-f $REPO_ROOT/rtl/math/filelists/math_multiplier_wallace_tree_032.f
-f $REPO_ROOT/rtl/math/filelists/math_multiplier_wallace_tree_csa_008.f
-f $REPO_ROOT/rtl/math/filelists/math_multiplier_wallace_tree_csa_016.f
-f $REPO_ROOT/rtl/math/filelists/math_multiplier_wallace_tree_csa_032.f
-f $REPO_ROOT/rtl/math/filelists/math_subtractor_carry_lookahead.f
-f $REPO_ROOT/rtl/math/filelists/math_subtractor_full.f
-f $REPO_ROOT/rtl/math/filelists/math_subtractor_full_nbit.f
-f $REPO_ROOT/rtl/math/filelists/math_subtractor_half.f
-f $REPO_ROOT/rtl/math/filelists/math_subtractor_ripple_carry.f

# Modules that do not yet have their own per-module filelist. They were
# previously reachable ONLY because rtl/common/filelists/common_all.f hand-listed
# all 171 math sources; the split surfaced that gap. Listed directly here so the
# reorg loses no coverage -- each should eventually get its own .f so consumers
# can pull just what they need.
$REPO_ROOT/rtl/math/math_adder_han_carlson_016.sv
$REPO_ROOT/rtl/math/math_adder_han_carlson_022.sv
$REPO_ROOT/rtl/math/math_adder_han_carlson_032.sv
$REPO_ROOT/rtl/math/math_adder_han_carlson_044.sv
$REPO_ROOT/rtl/math/math_adder_han_carlson_048.sv
$REPO_ROOT/rtl/math/math_adder_han_carlson_072.sv
$REPO_ROOT/rtl/math/math_bf16_adder.sv
$REPO_ROOT/rtl/math/math_bf16_clamp.sv
$REPO_ROOT/rtl/math/math_bf16_comparator.sv
$REPO_ROOT/rtl/math/math_bf16_divider.sv
$REPO_ROOT/rtl/math/math_bf16_exp2.sv
$REPO_ROOT/rtl/math/math_bf16_exponent_adder.sv
$REPO_ROOT/rtl/math/math_bf16_fast_reciprocal.sv
$REPO_ROOT/rtl/math/math_bf16_fma.sv
$REPO_ROOT/rtl/math/math_bf16_gelu.sv
$REPO_ROOT/rtl/math/math_bf16_goldschmidt_div.sv
$REPO_ROOT/rtl/math/math_bf16_leaky_relu.sv
$REPO_ROOT/rtl/math/math_bf16_log2.sv
$REPO_ROOT/rtl/math/math_bf16_log2_scale.sv
$REPO_ROOT/rtl/math/math_bf16_mantissa_mult.sv
$REPO_ROOT/rtl/math/math_bf16_max.sv
$REPO_ROOT/rtl/math/math_bf16_max_tree.sv
$REPO_ROOT/rtl/math/math_bf16_max_tree_8.sv
$REPO_ROOT/rtl/math/math_bf16_min.sv
$REPO_ROOT/rtl/math/math_bf16_min_tree_8.sv
$REPO_ROOT/rtl/math/math_bf16_multiplier.sv
$REPO_ROOT/rtl/math/math_bf16_newton_raphson_recip.sv
$REPO_ROOT/rtl/math/math_bf16_reciprocal.sv
$REPO_ROOT/rtl/math/math_bf16_relu.sv
$REPO_ROOT/rtl/math/math_bf16_scale_to_int8.sv
$REPO_ROOT/rtl/math/math_bf16_sigmoid.sv
$REPO_ROOT/rtl/math/math_bf16_silu.sv
$REPO_ROOT/rtl/math/math_bf16_softmax_8.sv
$REPO_ROOT/rtl/math/math_bf16_tanh.sv
$REPO_ROOT/rtl/math/math_bf16_to_fp16.sv
$REPO_ROOT/rtl/math/math_bf16_to_fp32.sv
$REPO_ROOT/rtl/math/math_bf16_to_fp8_e4m3.sv
$REPO_ROOT/rtl/math/math_bf16_to_fp8_e5m2.sv
$REPO_ROOT/rtl/math/math_bf16_to_int.sv
$REPO_ROOT/rtl/math/math_compressor_4to2.sv
$REPO_ROOT/rtl/math/math_fp16_clamp.sv
$REPO_ROOT/rtl/math/math_fp16_comparator.sv
$REPO_ROOT/rtl/math/math_fp16_gelu.sv
$REPO_ROOT/rtl/math/math_fp16_leaky_relu.sv
$REPO_ROOT/rtl/math/math_fp16_max.sv
$REPO_ROOT/rtl/math/math_fp16_max_tree_8.sv
$REPO_ROOT/rtl/math/math_fp16_min.sv
$REPO_ROOT/rtl/math/math_fp16_min_tree_8.sv
$REPO_ROOT/rtl/math/math_fp16_relu.sv
$REPO_ROOT/rtl/math/math_fp16_sigmoid.sv
$REPO_ROOT/rtl/math/math_fp16_silu.sv
$REPO_ROOT/rtl/math/math_fp16_softmax_8.sv
$REPO_ROOT/rtl/math/math_fp16_tanh.sv
$REPO_ROOT/rtl/math/math_fp16_to_bf16.sv
$REPO_ROOT/rtl/math/math_fp16_to_fp32.sv
$REPO_ROOT/rtl/math/math_fp16_to_fp8_e4m3.sv
$REPO_ROOT/rtl/math/math_fp16_to_fp8_e5m2.sv
$REPO_ROOT/rtl/math/math_fp32_clamp.sv
$REPO_ROOT/rtl/math/math_fp32_comparator.sv
$REPO_ROOT/rtl/math/math_fp32_gelu.sv
$REPO_ROOT/rtl/math/math_fp32_leaky_relu.sv
$REPO_ROOT/rtl/math/math_fp32_max.sv
$REPO_ROOT/rtl/math/math_fp32_max_tree_8.sv
$REPO_ROOT/rtl/math/math_fp32_min.sv
$REPO_ROOT/rtl/math/math_fp32_min_tree_8.sv
$REPO_ROOT/rtl/math/math_fp32_relu.sv
$REPO_ROOT/rtl/math/math_fp32_sigmoid.sv
$REPO_ROOT/rtl/math/math_fp32_silu.sv
$REPO_ROOT/rtl/math/math_fp32_softmax_8.sv
$REPO_ROOT/rtl/math/math_fp32_tanh.sv
$REPO_ROOT/rtl/math/math_fp32_to_bf16.sv
$REPO_ROOT/rtl/math/math_fp32_to_fp16.sv
$REPO_ROOT/rtl/math/math_fp32_to_fp8_e4m3.sv
$REPO_ROOT/rtl/math/math_fp32_to_fp8_e5m2.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_adder.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_clamp.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_comparator.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_exponent_adder.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_fma.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_gelu.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_leaky_relu.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_mantissa_mult.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_max.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_max_tree_8.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_min.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_min_tree_8.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_multiplier.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_relu.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_sigmoid.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_silu.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_softmax_8.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_tanh.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_to_bf16.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_to_fp16.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_to_fp32.sv
$REPO_ROOT/rtl/math/math_fp8_e4m3_to_fp8_e5m2.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_adder.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_clamp.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_comparator.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_exponent_adder.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_fma.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_gelu.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_leaky_relu.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_mantissa_mult.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_max.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_max_tree_8.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_min.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_min_tree_8.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_multiplier.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_relu.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_sigmoid.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_silu.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_softmax_8.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_tanh.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_to_bf16.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_to_fp16.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_to_fp32.sv
$REPO_ROOT/rtl/math/math_fp8_e5m2_to_fp8_e4m3.sv
$REPO_ROOT/rtl/math/math_ieee754_2008_fp16_adder.sv
$REPO_ROOT/rtl/math/math_ieee754_2008_fp16_exponent_adder.sv
$REPO_ROOT/rtl/math/math_ieee754_2008_fp16_fma.sv
$REPO_ROOT/rtl/math/math_ieee754_2008_fp16_mantissa_mult.sv
$REPO_ROOT/rtl/math/math_ieee754_2008_fp16_multiplier.sv
$REPO_ROOT/rtl/math/math_ieee754_2008_fp32_adder.sv
$REPO_ROOT/rtl/math/math_ieee754_2008_fp32_exponent_adder.sv
$REPO_ROOT/rtl/math/math_ieee754_2008_fp32_fma.sv
$REPO_ROOT/rtl/math/math_ieee754_2008_fp32_mantissa_mult.sv
$REPO_ROOT/rtl/math/math_ieee754_2008_fp32_multiplier.sv
$REPO_ROOT/rtl/math/math_int_to_bf16.sv
$REPO_ROOT/rtl/math/math_multiplier_dadda_4to2_008.sv
$REPO_ROOT/rtl/math/math_multiplier_dadda_4to2_011.sv
$REPO_ROOT/rtl/math/math_multiplier_dadda_4to2_024.sv
$REPO_ROOT/rtl/math/math_prefix_cell.sv
$REPO_ROOT/rtl/math/math_prefix_cell_gray.sv
