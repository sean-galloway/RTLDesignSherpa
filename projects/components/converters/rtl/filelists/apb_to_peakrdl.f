# Filelist for apb_to_peakrdl module
# Location: projects/components/converters/rtl/filelists/apb_to_peakrdl.f
# Purpose: APB to PeakRDL cmd/rsp shim (used by the NexysA7 ddr2-char harness)

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Sub-blocks (consumers -f this file rather than hand-listing them)
-f $REPO_ROOT/rtl/amba/filelists/apb4_slave_cdc.f
-f $CONVERTERS_ROOT/rtl/filelists/peakrdl_to_cmdrsp.f

$CONVERTERS_ROOT/rtl/apb_to_peakrdl.sv
