# Filelist for axi4_to_axil4 module
# Location: projects/components/converters/rtl/filelists/axi4_to_axil4.f
# Purpose: AXI4 to AXI4-Lite converter (rd+wr)

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Sub-blocks (consumers -f this file rather than hand-listing them)
-f $CONVERTERS_ROOT/rtl/filelists/axi4_to_axil4_rd.f
-f $CONVERTERS_ROOT/rtl/filelists/axi4_to_axil4_wr.f

$CONVERTERS_ROOT/rtl/axi4_to_axil4.sv
