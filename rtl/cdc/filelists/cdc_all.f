# ==============================================================================
# RTL CDC Library - Master Filelist for Verilator Lint
# ==============================================================================
#
# Purpose: Complete list of all CDC library modules for linting
# Usage:   verilator --lint-only -f filelists/cdc_all.f
#
# Notes:
#   - The counterpart of rtl/common/filelists/common_all.f and
#     rtl/amba/filelists/amba_all.f. Those two used to carry these modules;
#     AMBA-CDC-REORG moved them here, so they lint from this list now.
#   - glitch_free_n_dff_arn and sync_pulse moved in from rtl/common 2026-08-08.
#   - Shared dependencies (counter_bin, fifo_control, leading_one_trailing_one,
#     gaxi_skid_buffer) stay in their owning areas and arrive through the
#     per-module -f includes below.
#
# ==============================================================================

+incdir+$REPO_ROOT/rtl/amba/includes

# Gray / Johnson coders -- they exist to make the crossings below safe
-f $REPO_ROOT/rtl/cdc/filelists/bin2gray.f
-f $REPO_ROOT/rtl/cdc/filelists/gray2bin.f
-f $REPO_ROOT/rtl/cdc/filelists/johnson2bin.f
-f $REPO_ROOT/rtl/cdc/filelists/counter_bingray.f
-f $REPO_ROOT/rtl/cdc/filelists/counter_johnson.f

# Synchronizer and handshakes
-f $REPO_ROOT/rtl/cdc/filelists/cdc_synchronizer.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_2_phase_handshake.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_4_phase_handshake.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_open_loop.f

# Asynchronous FIFOs
-f $REPO_ROOT/rtl/cdc/filelists/fifo_async.f
-f $REPO_ROOT/rtl/cdc/filelists/gaxi_fifo_async.f
-f $REPO_ROOT/rtl/cdc/filelists/gaxi_skid_buffer_async.f
$REPO_ROOT/rtl/cdc/glitch_free_n_dff_arn.sv
$REPO_ROOT/rtl/cdc/sync_pulse.sv
