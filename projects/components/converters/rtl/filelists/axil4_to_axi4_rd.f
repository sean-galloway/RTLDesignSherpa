# Filelist for axil4_to_axi4_rd module
# Location: projects/components/converters/rtl/filelists/axil4_to_axi4_rd.f
# Purpose: AXI4-Lite to AXI4 read protocol converter (add burst fields)

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# AXIL4 to AXI4 read converter
$CONVERTERS_ROOT/rtl/axil4_to_axi4_rd.sv
