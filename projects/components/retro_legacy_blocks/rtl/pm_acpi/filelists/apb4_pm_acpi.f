# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Filelist: apb4_pm_acpi.f
# Purpose: Complete file list for APB PM_ACPI module
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
-f $REPO_ROOT/rtl/amba/filelists/apb4_slave_cdc.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_2_phase_handshake.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_4_phase_handshake.f

# Layer 2: CMD/RSP to PeakRDL Adapter
-f $REPO_ROOT/projects/components/converters/rtl/filelists/peakrdl_to_cmdrsp.f

# Package (must come first)
$RETRO_ROOT/rtl/pm_acpi/pm_acpi_regs_pkg.sv

# Register file (PeakRDL generated)
$RETRO_ROOT/rtl/pm_acpi/pm_acpi_regs.sv

# PM_ACPI core (power management logic)
$RETRO_ROOT/rtl/pm_acpi/pm_acpi_core.sv

# Config register wrapper
$RETRO_ROOT/rtl/pm_acpi/pm_acpi_config_regs.sv

# Top-level APB wrapper
$RETRO_ROOT/rtl/pm_acpi/apb4_pm_acpi.sv
