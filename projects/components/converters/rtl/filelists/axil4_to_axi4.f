# Filelist for axil4_to_axi4 module
# Location: projects/components/converters/rtl/filelists/axil4_to_axi4.f
# Purpose: AXI4-Lite to AXI4 converter (rd+wr)

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Sub-blocks (consumers -f this file rather than hand-listing them)
-f $CONVERTERS_ROOT/rtl/filelists/axil4_to_axi4_rd.f
-f $CONVERTERS_ROOT/rtl/filelists/axil4_to_axi4_wr.f

$CONVERTERS_ROOT/rtl/axil4_to_axi4.sv
