# Filelist for axil4_to_axi4_wr module
# Location: projects/components/converters/rtl/filelists/axil4_to_axi4_wr.f
# Purpose: AXI4-Lite to AXI4 write protocol converter (add burst fields)

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# AXIL4 to AXI4 write converter
$CONVERTERS_ROOT/rtl/axil4_to_axi4_wr.sv
