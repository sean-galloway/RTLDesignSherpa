# Filelist for peakrdl_to_cmdrsp module
# Location: projects/components/converters/rtl/filelists/peakrdl_to_cmdrsp.f
# Purpose: PeakRDL passthrough to CMD/RSP valid/ready adapter

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# PeakRDL to CMD/RSP adapter
$CONVERTERS_ROOT/rtl/peakrdl_to_cmdrsp.sv
