# Filelist for axi_data_upsize module
# Location: projects/components/converters/rtl/filelists/axi_data_upsize.f
# Purpose: AXI data width upsizer (narrow → wide)

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/rtl/common

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# AXI data upsizer module
$CONVERTERS_ROOT/rtl/axi_data_upsize.sv
