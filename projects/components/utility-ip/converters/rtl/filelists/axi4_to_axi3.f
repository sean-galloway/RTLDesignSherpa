# Filelist for axi4_to_axi3 module
# Location: projects/components/utility-ip/converters/rtl/filelists/axi4_to_axi3.f
# Purpose: AXI4 to AXI3 converter (rd+wr top wrapper)

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Sub-blocks
-f $CONVERTERS_ROOT/rtl/filelists/axi4_to_axi3_rd.f
-f $CONVERTERS_ROOT/rtl/filelists/axi4_to_axi3_wr.f

$CONVERTERS_ROOT/rtl/axi4_to_axi3.sv
