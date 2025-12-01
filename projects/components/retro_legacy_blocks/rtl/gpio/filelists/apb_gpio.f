# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Filelist: apb_gpio.f
# Purpose: Complete file list for APB GPIO module
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
$RETRO_ROOT/rtl/gpio/gpio_regs_pkg.sv

# Register file (PeakRDL generated)
$RETRO_ROOT/rtl/gpio/gpio_regs.sv

# GPIO core (I/O logic, interrupts)
$RETRO_ROOT/rtl/gpio/gpio_core.sv

# Config register wrapper
$RETRO_ROOT/rtl/gpio/gpio_config_regs.sv

# Top-level APB wrapper
$RETRO_ROOT/rtl/gpio/apb_gpio.sv
