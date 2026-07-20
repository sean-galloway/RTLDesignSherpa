# ==============================================================================
# RTL Common Library - Master Filelist for Verilator Lint
# ==============================================================================
#
# Purpose: Complete list of all Common library modules for linting
# Usage:   verilator --lint-only -f filelists/common_all.f
#
# Notes:
#   - Files listed in alphabetical order for maintainability
#   - Include paths added via command line: -I$REPO_ROOT/rtl/amba/includes
#   - No package dependencies (Common is self-contained)
#
# ==============================================================================

# Arbiters
$REPO_ROOT/rtl/common/arbiter_priority_encoder.sv
$REPO_ROOT/rtl/common/arbiter_round_robin.sv
$REPO_ROOT/rtl/common/arbiter_round_robin_simple.sv
$REPO_ROOT/rtl/common/arbiter_round_robin_weighted.sv
$REPO_ROOT/rtl/common/arbiter_single_client.sv

# Binary/Gray Code Converters
$REPO_ROOT/rtl/common/bin2gray.sv
$REPO_ROOT/rtl/common/bin_to_bcd.sv
$REPO_ROOT/rtl/common/gray2bin.sv
$REPO_ROOT/rtl/common/johnson2bin.sv

# CAM
$REPO_ROOT/rtl/common/cam_tag.sv

# Clock Utilities
$REPO_ROOT/rtl/common/clock_divider.sv
$REPO_ROOT/rtl/common/clock_gate_ctrl.sv
$REPO_ROOT/rtl/common/clock_pulse.sv
$REPO_ROOT/rtl/common/icg.sv

# Counters
$REPO_ROOT/rtl/common/counter.sv
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/counter_bin_load.sv
$REPO_ROOT/rtl/common/counter_bingray.sv
$REPO_ROOT/rtl/common/counter_freq_invariant.sv
$REPO_ROOT/rtl/common/counter_johnson.sv
$REPO_ROOT/rtl/common/counter_load_clear.sv
$REPO_ROOT/rtl/common/counter_ring.sv
$REPO_ROOT/rtl/common/count_leading_zeros.sv
$REPO_ROOT/rtl/common/count_trailing_zeros.sv

# Data Integrity (CRC, ECC, Parity)
$REPO_ROOT/rtl/common/dataint_checksum.sv
$REPO_ROOT/rtl/common/dataint_crc.sv
$REPO_ROOT/rtl/common/dataint_crc_xor_shift.sv
$REPO_ROOT/rtl/common/dataint_crc_xor_shift_cascade.sv
$REPO_ROOT/rtl/common/dataint_ecc_hamming_decode_secded.sv
$REPO_ROOT/rtl/common/dataint_ecc_hamming_encode_secded.sv
$REPO_ROOT/rtl/common/dataint_parity.sv

# Debounce and Glitch-Free
$REPO_ROOT/rtl/common/debounce.sv
$REPO_ROOT/rtl/common/glitch_free_n_dff_arn.sv

# Encoders/Decoders
$REPO_ROOT/rtl/common/decoder.sv
$REPO_ROOT/rtl/common/encoder.sv
$REPO_ROOT/rtl/common/encoder_priority_enable.sv
$REPO_ROOT/rtl/common/hex_to_7seg.sv

# FIFOs
$REPO_ROOT/rtl/common/fifo_async.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/common/fifo_sync.sv

# Find First/Last Set
$REPO_ROOT/rtl/common/find_first_set.sv
$REPO_ROOT/rtl/common/find_last_set.sv
$REPO_ROOT/rtl/common/leading_one_trailing_one.sv

# Math - Adders (Basic)
$REPO_ROOT/rtl/common/math_adder_pg_chain.sv
$REPO_ROOT/rtl/common/math_adder_carry_save.sv
$REPO_ROOT/rtl/common/math_adder_carry_save_nbit.sv
$REPO_ROOT/rtl/common/math_adder_full.sv
$REPO_ROOT/rtl/common/math_adder_full_nbit.sv
$REPO_ROOT/rtl/common/math_adder_half.sv
$REPO_ROOT/rtl/common/math_adder_ripple_carry.sv
$REPO_ROOT/rtl/common/math_addsub_full_nbit.sv

# Math - Adders (Brent-Kung)
$REPO_ROOT/rtl/common/math_adder_brent_kung_008.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_016.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_032.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_064.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_bitwisepg.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_black.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_gray.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_grouppg_008.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_grouppg_016.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_grouppg_032.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_grouppg_064.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_pg.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_sum.sv

# Math - Multipliers
$REPO_ROOT/rtl/common/math_compressor_4to2.sv
$REPO_ROOT/rtl/common/math_multiplier_basic_cell.sv
$REPO_ROOT/rtl/common/math_multiplier_carry_save.sv
$REPO_ROOT/rtl/common/math_multiplier_dadda_4to2_008.sv
$REPO_ROOT/rtl/common/math_multiplier_dadda_4to2_011.sv
$REPO_ROOT/rtl/common/math_multiplier_dadda_4to2_024.sv
$REPO_ROOT/rtl/common/math_multiplier_dadda_tree_008.sv
$REPO_ROOT/rtl/common/math_multiplier_dadda_tree_016.sv
$REPO_ROOT/rtl/common/math_multiplier_dadda_tree_032.sv
$REPO_ROOT/rtl/common/math_multiplier_wallace_tree_008.sv
$REPO_ROOT/rtl/common/math_multiplier_wallace_tree_016.sv
$REPO_ROOT/rtl/common/math_multiplier_wallace_tree_032.sv
$REPO_ROOT/rtl/common/math_multiplier_wallace_tree_csa_008.sv
$REPO_ROOT/rtl/common/math_multiplier_wallace_tree_csa_016.sv
$REPO_ROOT/rtl/common/math_multiplier_wallace_tree_csa_032.sv

# Math - Subtractors
$REPO_ROOT/rtl/common/math_subtractor_carry_lookahead.sv
$REPO_ROOT/rtl/common/math_subtractor_full.sv
$REPO_ROOT/rtl/common/math_subtractor_full_nbit.sv
$REPO_ROOT/rtl/common/math_subtractor_half.sv
$REPO_ROOT/rtl/common/math_subtractor_ripple_carry.sv

# PWM
$REPO_ROOT/rtl/common/pwm.sv

# Reset and Synchronization
$REPO_ROOT/rtl/common/reset_sync.sv
$REPO_ROOT/rtl/common/sync_pulse.sv

# Shifters
$REPO_ROOT/rtl/common/reverse_vector.sv
$REPO_ROOT/rtl/common/shifter_barrel.sv
$REPO_ROOT/rtl/common/shifter_beat_pack.sv
$REPO_ROOT/rtl/common/shifter_lfsr.sv
$REPO_ROOT/rtl/common/shifter_lfsr_fibonacci.sv
$REPO_ROOT/rtl/common/shifter_lfsr_galois.sv
$REPO_ROOT/rtl/common/shifter_universal.sv

# Sort
$REPO_ROOT/rtl/common/sort.sv

# ==============================================================================
# Math - Adders (Han-Carlson)
$REPO_ROOT/rtl/common/math_adder_han_carlson_016.sv
$REPO_ROOT/rtl/common/math_adder_han_carlson_022.sv
$REPO_ROOT/rtl/common/math_adder_han_carlson_032.sv
$REPO_ROOT/rtl/common/math_adder_han_carlson_044.sv
$REPO_ROOT/rtl/common/math_adder_han_carlson_048.sv
$REPO_ROOT/rtl/common/math_adder_han_carlson_072.sv

# Math - Floating Point (BF16)
$REPO_ROOT/rtl/common/math_bf16_adder.sv
$REPO_ROOT/rtl/common/math_bf16_clamp.sv
$REPO_ROOT/rtl/common/math_bf16_comparator.sv
$REPO_ROOT/rtl/common/math_bf16_divider.sv
$REPO_ROOT/rtl/common/math_bf16_exp2.sv
$REPO_ROOT/rtl/common/math_bf16_exponent_adder.sv
$REPO_ROOT/rtl/common/math_bf16_fast_reciprocal.sv
$REPO_ROOT/rtl/common/math_bf16_fma.sv
$REPO_ROOT/rtl/common/math_bf16_gelu.sv
$REPO_ROOT/rtl/common/math_bf16_goldschmidt_div.sv
$REPO_ROOT/rtl/common/math_bf16_leaky_relu.sv
$REPO_ROOT/rtl/common/math_bf16_log2.sv
$REPO_ROOT/rtl/common/math_bf16_log2_scale.sv
$REPO_ROOT/rtl/common/math_bf16_mantissa_mult.sv
$REPO_ROOT/rtl/common/math_bf16_max.sv
$REPO_ROOT/rtl/common/math_bf16_max_tree.sv
$REPO_ROOT/rtl/common/math_bf16_max_tree_8.sv
$REPO_ROOT/rtl/common/math_bf16_min.sv
$REPO_ROOT/rtl/common/math_bf16_min_tree_8.sv
$REPO_ROOT/rtl/common/math_bf16_multiplier.sv
$REPO_ROOT/rtl/common/math_bf16_newton_raphson_recip.sv
$REPO_ROOT/rtl/common/math_bf16_reciprocal.sv
$REPO_ROOT/rtl/common/math_bf16_relu.sv
$REPO_ROOT/rtl/common/math_bf16_scale_to_int8.sv
$REPO_ROOT/rtl/common/math_bf16_sigmoid.sv
$REPO_ROOT/rtl/common/math_bf16_silu.sv
$REPO_ROOT/rtl/common/math_bf16_softmax_8.sv
$REPO_ROOT/rtl/common/math_bf16_tanh.sv
$REPO_ROOT/rtl/common/math_bf16_to_fp16.sv
$REPO_ROOT/rtl/common/math_bf16_to_fp32.sv
$REPO_ROOT/rtl/common/math_bf16_to_fp8_e4m3.sv
$REPO_ROOT/rtl/common/math_bf16_to_fp8_e5m2.sv
$REPO_ROOT/rtl/common/math_bf16_to_int.sv
$REPO_ROOT/rtl/common/math_int_to_bf16.sv

# Math - Floating Point (FP16)
$REPO_ROOT/rtl/common/math_fp16_clamp.sv
$REPO_ROOT/rtl/common/math_fp16_comparator.sv
$REPO_ROOT/rtl/common/math_fp16_gelu.sv
$REPO_ROOT/rtl/common/math_fp16_leaky_relu.sv
$REPO_ROOT/rtl/common/math_fp16_max.sv
$REPO_ROOT/rtl/common/math_fp16_max_tree_8.sv
$REPO_ROOT/rtl/common/math_fp16_min.sv
$REPO_ROOT/rtl/common/math_fp16_min_tree_8.sv
$REPO_ROOT/rtl/common/math_fp16_relu.sv
$REPO_ROOT/rtl/common/math_fp16_sigmoid.sv
$REPO_ROOT/rtl/common/math_fp16_silu.sv
$REPO_ROOT/rtl/common/math_fp16_softmax_8.sv
$REPO_ROOT/rtl/common/math_fp16_tanh.sv
$REPO_ROOT/rtl/common/math_fp16_to_bf16.sv
$REPO_ROOT/rtl/common/math_fp16_to_fp32.sv
$REPO_ROOT/rtl/common/math_fp16_to_fp8_e4m3.sv
$REPO_ROOT/rtl/common/math_fp16_to_fp8_e5m2.sv

# Math - Floating Point (FP32)
$REPO_ROOT/rtl/common/math_fp32_clamp.sv
$REPO_ROOT/rtl/common/math_fp32_comparator.sv
$REPO_ROOT/rtl/common/math_fp32_gelu.sv
$REPO_ROOT/rtl/common/math_fp32_leaky_relu.sv
$REPO_ROOT/rtl/common/math_fp32_max.sv
$REPO_ROOT/rtl/common/math_fp32_max_tree_8.sv
$REPO_ROOT/rtl/common/math_fp32_min.sv
$REPO_ROOT/rtl/common/math_fp32_min_tree_8.sv
$REPO_ROOT/rtl/common/math_fp32_relu.sv
$REPO_ROOT/rtl/common/math_fp32_sigmoid.sv
$REPO_ROOT/rtl/common/math_fp32_silu.sv
$REPO_ROOT/rtl/common/math_fp32_softmax_8.sv
$REPO_ROOT/rtl/common/math_fp32_tanh.sv
$REPO_ROOT/rtl/common/math_fp32_to_bf16.sv
$REPO_ROOT/rtl/common/math_fp32_to_fp16.sv
$REPO_ROOT/rtl/common/math_fp32_to_fp8_e4m3.sv
$REPO_ROOT/rtl/common/math_fp32_to_fp8_e5m2.sv

# Math - Floating Point (FP8 E4M3)
$REPO_ROOT/rtl/common/math_fp8_e4m3_adder.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_clamp.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_comparator.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_exponent_adder.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_fma.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_gelu.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_leaky_relu.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_mantissa_mult.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_max.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_max_tree_8.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_min.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_min_tree_8.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_multiplier.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_relu.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_sigmoid.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_silu.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_softmax_8.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_tanh.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_to_bf16.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_to_fp16.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_to_fp32.sv
$REPO_ROOT/rtl/common/math_fp8_e4m3_to_fp8_e5m2.sv

# Math - Floating Point (FP8 E5M2)
$REPO_ROOT/rtl/common/math_fp8_e5m2_adder.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_clamp.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_comparator.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_exponent_adder.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_fma.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_gelu.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_leaky_relu.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_mantissa_mult.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_max.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_max_tree_8.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_min.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_min_tree_8.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_multiplier.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_relu.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_sigmoid.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_silu.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_softmax_8.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_tanh.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_to_bf16.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_to_fp16.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_to_fp32.sv
$REPO_ROOT/rtl/common/math_fp8_e5m2_to_fp8_e4m3.sv

# Math - Floating Point (IEEE 754-2008)
$REPO_ROOT/rtl/common/math_ieee754_2008_fp16_adder.sv
$REPO_ROOT/rtl/common/math_ieee754_2008_fp16_exponent_adder.sv
$REPO_ROOT/rtl/common/math_ieee754_2008_fp16_fma.sv
$REPO_ROOT/rtl/common/math_ieee754_2008_fp16_mantissa_mult.sv
$REPO_ROOT/rtl/common/math_ieee754_2008_fp16_multiplier.sv
$REPO_ROOT/rtl/common/math_ieee754_2008_fp32_adder.sv
$REPO_ROOT/rtl/common/math_ieee754_2008_fp32_exponent_adder.sv
$REPO_ROOT/rtl/common/math_ieee754_2008_fp32_fma.sv
$REPO_ROOT/rtl/common/math_ieee754_2008_fp32_mantissa_mult.sv
$REPO_ROOT/rtl/common/math_ieee754_2008_fp32_multiplier.sv

# Math - Modular
$REPO_ROOT/rtl/common/mod_3_compress.sv

# Math - Prefix Cells
$REPO_ROOT/rtl/common/math_prefix_cell.sv
$REPO_ROOT/rtl/common/math_prefix_cell_gray.sv

# End of filelist
# ==============================================================================
