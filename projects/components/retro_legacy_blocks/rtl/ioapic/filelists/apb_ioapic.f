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

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/apb_slave_cdc.f
-f $REPO_ROOT/rtl/amba/filelists/cdc_2_phase_handshake.f
-f $REPO_ROOT/rtl/amba/filelists/cdc_4_phase_handshake.f

# PeakRDL adapter
-f $REPO_ROOT/projects/components/converters/rtl/filelists/peakrdl_to_cmdrsp.f

# PeakRDL generated package and register block
$REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_regs_pkg.sv
$REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_regs.sv

# IOAPIC core modules
$REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_core.sv
$REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_config_regs.sv

# APB top-level wrapper
$REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/apb_ioapic.sv
