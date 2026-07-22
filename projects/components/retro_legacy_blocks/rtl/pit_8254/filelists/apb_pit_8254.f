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

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/apb_slave_cdc.f
-f $REPO_ROOT/rtl/amba/filelists/cdc_2_phase_handshake.f
-f $REPO_ROOT/rtl/amba/filelists/cdc_4_phase_handshake.f

# Layer 2: CMD/RSP to PeakRDL Adapter
-f $REPO_ROOT/projects/components/converters/rtl/filelists/peakrdl_to_cmdrsp.f

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
