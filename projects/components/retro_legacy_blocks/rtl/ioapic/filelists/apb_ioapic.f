# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Filelist: apb_ioapic.f
# Purpose: Complete file list for APB IOAPIC module
#
# Usage: Source this file in simulation/synthesis tools

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Low-level dependencies (for APB slave modules)
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/shared/cdc_handshake.sv

# APB slave infrastructure
$REPO_ROOT/rtl/amba/apb/apb_slave_cdc.sv
$REPO_ROOT/rtl/amba/apb/apb_slave.sv

# PeakRDL adapter
$REPO_ROOT/projects/components/converters/rtl/peakrdl_to_cmdrsp.sv

# PeakRDL generated package and register block
$REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_regs_pkg.sv
$REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_regs.sv

# IOAPIC core modules
$REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_core.sv
$REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_config_regs.sv

# APB top-level wrapper
$REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/apb_ioapic.sv
