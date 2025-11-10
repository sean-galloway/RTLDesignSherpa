# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Filelist: apb_pit_8254.f
# Purpose: Complete file list for APB 8254 PIT module
#
# Usage: Source this file in simulation/synthesis tools

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Low-level dependencies (for APB slave modules)
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/shared/cdc_handshake.sv

# Layer 1: APB Slave (APB → CMD/RSP interface)
$REPO_ROOT/rtl/amba/apb/apb_slave.sv
$REPO_ROOT/rtl/amba/apb/apb_slave_cdc.sv

# Layer 2: CMD/RSP to PeakRDL Adapter
$REPO_ROOT/projects/components/converters/rtl/peakrdl_to_cmdrsp.sv

# Package (must come first)
$RETRO_ROOT/rtl/pit_8254/pit_regs_pkg.sv

# Register file (PeakRDL generated)
$RETRO_ROOT/rtl/pit_8254/pit_regs.sv

# Counter core
$RETRO_ROOT/rtl/pit_8254/pit_counter.sv

# PIT core (3-counter array)
$RETRO_ROOT/rtl/pit_8254/pit_core.sv

# Config register wrapper
$RETRO_ROOT/rtl/pit_8254/pit_config_regs.sv

# Top-level APB wrapper
$RETRO_ROOT/rtl/pit_8254/apb_pit_8254.sv
