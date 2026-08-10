# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Filelist: apb4_hpet.f
# Purpose: Complete file list for APB HPET module
#
# Usage: Source this file in simulation/synthesis tools

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Common modules
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f

# GAXI modules for CDC
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_2_phase_handshake.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_4_phase_handshake.f

# APB modules
-f $REPO_ROOT/rtl/amba/filelists/apb4_slave.f
-f $REPO_ROOT/rtl/amba/filelists/apb4_slave_cdc.f

# PeakRDL adapter (from converters component)
-f $REPO_ROOT/projects/components/converters/rtl/filelists/peakrdl_to_cmdrsp.f

# HPET modules (PeakRDL-based configuration registers)
$RETRO_ROOT/rtl/hpet/hpet_regs_pkg.sv
$RETRO_ROOT/rtl/hpet/hpet_regs.sv
$RETRO_ROOT/rtl/hpet/hpet_core.sv
$RETRO_ROOT/rtl/hpet/hpet_config_regs.sv
$RETRO_ROOT/rtl/hpet/apb4_hpet.sv
