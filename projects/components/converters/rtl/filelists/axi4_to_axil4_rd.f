# Filelist for axi4_to_axil4_rd module
# Location: projects/components/converters/rtl/filelists/axi4_to_axil4_rd.f
# Purpose: AXI4 to AXI4-Lite read protocol converter (burst decomposition)

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# AXI4 to AXIL4 read converter
$CONVERTERS_ROOT/rtl/axi4_to_axil4_rd.sv
