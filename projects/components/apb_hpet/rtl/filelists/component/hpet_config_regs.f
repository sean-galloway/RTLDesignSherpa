# HPET Configuration Register Wrapper File List
# Location: rtl/amba/components/hpet/filelists/component/hpet_config_regs.f
# Purpose: Wrapper that connects PeakRDL register block to HPET core

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Include PeakRDL register block
-f $REPO_ROOT/rtl/amba/components/hpet/filelists/component/hpet_regs.f

# Wrapper module
$REPO_ROOT/rtl/amba/components/hpet/hpet_config_regs.sv
