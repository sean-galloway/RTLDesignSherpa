# Filelist for peakrdl_to_cmdrsp module
# Location: projects/components/utility-ip/converters/rtl/filelists/peakrdl_to_cmdrsp.f
# Purpose: PeakRDL passthrough to CMD/RSP valid/ready adapter

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Boundary reset synchronizer (block input reset is async-assert,
# synchronized internally; complete closure)
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f

# PeakRDL to CMD/RSP adapter
$CONVERTERS_ROOT/rtl/peakrdl_to_cmdrsp.sv
