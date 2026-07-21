# HPET Configuration Register Wrapper File List
# Location: projects/components/retro_legacy_blocks/rtl/hpet/filelists/component/hpet_config_regs.f
# Purpose: Wrapper that connects PeakRDL register block to HPET core

# Header files with macros (MUST be compiled first)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Include PeakRDL register block
-f $RETRO_ROOT/rtl/hpet/filelists/component/hpet_regs.f

# The wrapper instantiates peakrdl_to_cmdrsp; pull it in via the converters
# component's own filelist rather than hand-listing its sources.
-f $CONVERTERS_ROOT/rtl/filelists/peakrdl_to_cmdrsp.f

# Wrapper module
$RETRO_ROOT/rtl/hpet/hpet_config_regs.sv
