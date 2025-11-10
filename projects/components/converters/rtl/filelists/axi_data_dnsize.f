# Filelist for axi_data_dnsize module
# Location: projects/components/converters/rtl/filelists/axi_data_dnsize.f
# Purpose: AXI data width downsizer (wide → narrow)

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/rtl/common

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# AXI data downsizer module
$CONVERTERS_ROOT/rtl/axi_data_dnsize.sv
