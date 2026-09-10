# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Filelist: apb4_smbus.f
# Purpose: Complete file list for APB SMBus 2.0 Controller
#
# Usage: Pass this filelist to your simulator/synthesis tool
#   Example (Verilator): verilator -f apb4_smbus.f
#   Example (VCS): vcs -f apb4_smbus.f
#   Example (Vivado): read_verilog -sv [glob [read apb4_smbus.f]]

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/apb4_slave_cdc.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_2_phase_handshake.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_4_phase_handshake.f
-f $REPO_ROOT/rtl/common/filelists/fifo_sync.f
-f $REPO_ROOT/rtl/cdc/filelists/glitch_free_n_dff_arn.f

# PeakRDL adapter (from converters)
-f $REPO_ROOT/projects/components/converters/rtl/filelists/peakrdl_to_cmdrsp.f

# PeakRDL-generated registers. The .vlt comes FIRST and is not optional: it
# waives the two Verilator rules that only the generated block trips (see the
# file for why), without waiving them anywhere else.
$RETRO_ROOT/rtl/smbus/smbus_regs.vlt
$RETRO_ROOT/rtl/smbus/smbus_regs_pkg.sv
$RETRO_ROOT/rtl/smbus/smbus_regs.sv

# SMBus master engine: the transaction sequencer, the bit PHY it drives, the
# PEC engine and the FIFOs. Declared through smbus_core.f rather than listed
# here, so a consumer of the master engine alone gets the same closure.
-f $RETRO_ROOT/rtl/smbus/filelists/smbus_core.f

# Configuration registers wrapper (uses PeakRDL)
$RETRO_ROOT/rtl/smbus/smbus_config_regs.sv

# Top-level APB wrapper
$RETRO_ROOT/rtl/smbus/apb4_smbus.sv
