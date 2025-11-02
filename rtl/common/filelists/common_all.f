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

# Binary/Gray Code Converters
$REPO_ROOT/rtl/common/bin2gray.sv
$REPO_ROOT/rtl/common/bin_to_bcd.sv
$REPO_ROOT/rtl/common/gray2bin.sv
$REPO_ROOT/rtl/common/grayj2bin.sv

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
$REPO_ROOT/rtl/common/fifo_async_div2.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/common/fifo_sync.sv

# Find First/Last Set
$REPO_ROOT/rtl/common/find_first_set.sv
$REPO_ROOT/rtl/common/find_last_set.sv
$REPO_ROOT/rtl/common/leading_one_trailing_one.sv

# Math - Adders (Basic)
$REPO_ROOT/rtl/common/math_adder_carry_lookahead.sv
$REPO_ROOT/rtl/common/math_adder_carry_save.sv
$REPO_ROOT/rtl/common/math_adder_carry_save_nbit.sv
$REPO_ROOT/rtl/common/math_adder_full.sv
$REPO_ROOT/rtl/common/math_adder_full_nbit.sv
$REPO_ROOT/rtl/common/math_adder_half.sv
$REPO_ROOT/rtl/common/math_adder_kogge_stone_nbit.sv
$REPO_ROOT/rtl/common/math_adder_ripple_carry.sv
$REPO_ROOT/rtl/common/math_addsub_full_nbit.sv

# Math - Adders (Brent-Kung)
$REPO_ROOT/rtl/common/math_adder_brent_kung_008.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_016.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_032.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_bitwisepg.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_black.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_gray.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_grouppg_008.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_grouppg_016.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_grouppg_032.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_pg.sv
$REPO_ROOT/rtl/common/math_adder_brent_kung_sum.sv

# Math - Multipliers
$REPO_ROOT/rtl/common/math_multiplier_basic_cell.sv
$REPO_ROOT/rtl/common/math_multiplier_carry_save.sv
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
$REPO_ROOT/rtl/common/shifter_lfsr.sv
$REPO_ROOT/rtl/common/shifter_lfsr_fibonacci.sv
$REPO_ROOT/rtl/common/shifter_lfsr_galois.sv
$REPO_ROOT/rtl/common/shifter_universal.sv

# Sort
$REPO_ROOT/rtl/common/sort.sv

# ==============================================================================
# End of filelist
# ==============================================================================
