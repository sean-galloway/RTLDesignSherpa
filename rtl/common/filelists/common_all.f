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

# Binary/BCD Converter
# (the Gray/Johnson coders moved to rtl/cdc -- see rtl/cdc/filelists/cdc_all.f)
$REPO_ROOT/rtl/common/bin_to_bcd.sv

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
$REPO_ROOT/rtl/common/counter_freq_invariant.sv
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
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/common/fifo_sync.sv

# Find First/Last Set
$REPO_ROOT/rtl/common/find_first_set.sv
$REPO_ROOT/rtl/common/find_last_set.sv
$REPO_ROOT/rtl/common/leading_one_trailing_one.sv

# Math - Adders (Basic)
# The math library now lives in rtl/math (see rtl/math/filelists/).
# -f its aggregate rather than hand-listing 171 sources here.
-f $REPO_ROOT/rtl/math/filelists/math_all.f

# Math - Adders (Brent-Kung)

# Math - Multipliers

# Math - Subtractors

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

# Math - Floating Point (BF16)

# Math - Floating Point (FP16)

# Math - Floating Point (FP32)

# Math - Floating Point (FP8 E4M3)

# Math - Floating Point (FP8 E5M2)

# Math - Floating Point (IEEE 754-2008)

# Math - Modular
$REPO_ROOT/rtl/common/mod_3_compress.sv

# Math - Prefix Cells

# End of filelist
# ==============================================================================
