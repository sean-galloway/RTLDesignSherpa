# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Filelist: apb_smbus.f
# Purpose: Complete file list for APB SMBus 2.0 Controller
#
# Usage: Pass this filelist to your simulator/synthesis tool
#   Example (Verilator): verilator -f apb_smbus.f
#   Example (VCS): vcs -f apb_smbus.f
#   Example (Vivado): read_verilog -sv [glob [read apb_smbus.f]]

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Common infrastructure
$REPO_ROOT/rtl/common/fifo_sync.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/common/counter_bin.sv

# Low-level dependencies (for APB slave modules)
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/shared/cdc_handshake.sv

# APB slave infrastructure
$REPO_ROOT/rtl/amba/apb/apb_slave.sv
$REPO_ROOT/rtl/amba/apb/apb_slave_cdc.sv

# PeakRDL adapter (from converters)
$REPO_ROOT/projects/components/converters/rtl/peakrdl_to_cmdrsp.sv

# PeakRDL-generated registers
$RETRO_ROOT/rtl/smbus/smbus_regs_pkg.sv
$RETRO_ROOT/rtl/smbus/smbus_regs.sv

# SMBus-specific modules
$RETRO_ROOT/rtl/smbus/smbus_pec.sv
$RETRO_ROOT/rtl/smbus/simple_fifo.sv
$RETRO_ROOT/rtl/smbus/smbus_core.sv

# Configuration registers wrapper (uses PeakRDL)
$RETRO_ROOT/rtl/smbus/smbus_config_regs.sv

# Top-level APB wrapper
$RETRO_ROOT/rtl/smbus/apb_smbus.sv
