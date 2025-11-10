# Filelist for axi4_to_axil4_wr module
# Location: projects/components/converters/rtl/filelists/axi4_to_axil4_wr.f
# Purpose: AXI4 to AXI4-Lite write protocol converter (burst decomposition)

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# AXI4 to AXIL4 write converter
$CONVERTERS_ROOT/rtl/axi4_to_axil4_wr.sv
