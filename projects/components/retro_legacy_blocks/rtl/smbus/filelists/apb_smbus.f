# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# File list for APB SMBus 2.0 Controller
#
# Usage: Pass this filelist to your simulator/synthesis tool
#   Example (Verilator): verilator -f apb_smbus.f
#   Example (VCS): vcs -f apb_smbus.f
#   Example (Vivado): read_verilog -sv [glob [read apb_smbus.f]]

#+incdir+${RTL_ROOT}/common
#+incdir+${RTL_ROOT}/amba

# Common infrastructure
${RTL_ROOT}/common/fifo_sync.sv
${RTL_ROOT}/common/fifo_control.sv
${RTL_ROOT}/common/counter_bin.sv

# APB slave infrastructure
${RTL_ROOT}/amba/apb/apb_slave.sv
${RTL_ROOT}/amba/apb/apb_slave_cdc.sv

# PeakRDL adapter (from converters)
${RTL_ROOT}/converters/rtl/peakrdl_to_cmdrsp.sv

# PeakRDL-generated registers
${RTL_ROOT}/retro_legacy_blocks/rtl/smbus/smbus_regs_pkg.sv
${RTL_ROOT}/retro_legacy_blocks/rtl/smbus/smbus_regs.sv

# SMBus-specific modules
${RTL_ROOT}/retro_legacy_blocks/rtl/smbus/smbus_pec.sv
${RTL_ROOT}/retro_legacy_blocks/rtl/smbus/simple_fifo.sv
${RTL_ROOT}/retro_legacy_blocks/rtl/smbus/smbus_core.sv

# Configuration registers wrapper (uses PeakRDL)
${RTL_ROOT}/retro_legacy_blocks/rtl/smbus/smbus_config_regs.sv

# Top-level APB wrapper
${RTL_ROOT}/retro_legacy_blocks/rtl/smbus/apb_smbus.sv
