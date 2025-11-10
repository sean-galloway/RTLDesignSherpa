# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Filelist: apb_hpet.f
# Purpose: Complete file list for APB HPET module
#
# Usage: Source this file in simulation/synthesis tools

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Common modules
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv

# GAXI modules for CDC
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/shared/cdc_handshake.sv

# APB modules
$REPO_ROOT/rtl/amba/apb/apb_slave.sv
$REPO_ROOT/rtl/amba/apb/apb_slave_cdc.sv

# PeakRDL adapter (from converters component)
$REPO_ROOT/projects/components/converters/rtl/peakrdl_to_cmdrsp.sv

# HPET modules (PeakRDL-based configuration registers)
$RETRO_ROOT/rtl/hpet/hpet_regs_pkg.sv
$RETRO_ROOT/rtl/hpet/hpet_regs.sv
$RETRO_ROOT/rtl/hpet/hpet_core.sv
$RETRO_ROOT/rtl/hpet/hpet_config_regs.sv
$RETRO_ROOT/rtl/hpet/apb_hpet.sv
