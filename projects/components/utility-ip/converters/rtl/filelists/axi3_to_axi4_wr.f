# Filelist for axi3_to_axi4_wr module
# Location: projects/components/utility-ip/converters/rtl/filelists/axi3_to_axi4_wr.f
# Purpose: AXI3 to AXI4 write protocol converter (WID strip under single-active contract)

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# AXI3 to AXI4 write converter
$CONVERTERS_ROOT/rtl/axi3_to_axi4_wr.sv
