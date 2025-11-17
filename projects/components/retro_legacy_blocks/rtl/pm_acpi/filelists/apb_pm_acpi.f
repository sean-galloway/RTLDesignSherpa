# =============================================================================
# PM_ACPI APB Wrapper Filelist
# =============================================================================
# Complete filelist for APB PM_ACPI (Power Management ACPI) controller
# Includes all dependencies for synthesis and simulation
# =============================================================================

# Common headers and packages (required for reset macros)
+incdir+${RTL_ROOT}/common

# PeakRDL generated package and register block
${RTL_ROOT}/pm_acpi/pm_acpi_regs_pkg.sv
${RTL_ROOT}/pm_acpi/pm_acpi_regs.sv

# PM_ACPI core modules
${RTL_ROOT}/pm_acpi/pm_acpi_core.sv
${RTL_ROOT}/pm_acpi/pm_acpi_config_regs.sv

# APB top-level wrapper
${RTL_ROOT}/pm_acpi/apb_pm_acpi.sv

# =============================================================================
# Dependencies
# =============================================================================
# This filelist requires the following external dependencies:
#
# 1. APB Slave Infrastructure:
#    - ${CONVERTERS_ROOT}/rtl/apb_slave.sv
#    - ${CONVERTERS_ROOT}/rtl/apb_slave_cdc.sv
#
# 2. PeakRDL Adapter:
#    - ${CONVERTERS_ROOT}/rtl/peakrdl_to_cmdrsp.sv
#
# 3. Reset Definitions:
#    - ${RTL_ROOT}/common/reset_defs.svh
#
# Include these from their respective filelists:
#    +incdir+${CONVERTERS_ROOT}/rtl
#    ${CONVERTERS_ROOT}/rtl/apb_slave.sv
#    ${CONVERTERS_ROOT}/rtl/apb_slave_cdc.sv
#    ${CONVERTERS_ROOT}/rtl/peakrdl_to_cmdrsp.sv
#
# Note: RTL_ROOT should be set to: projects/components/retro_legacy_blocks/rtl
#       CONVERTERS_ROOT should be set to: projects/components/converters
# =============================================================================
