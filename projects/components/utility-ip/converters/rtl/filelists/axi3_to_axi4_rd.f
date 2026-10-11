# Filelist for axi3_to_axi4_rd module
# Location: projects/components/utility-ip/converters/rtl/filelists/axi3_to_axi4_rd.f
# Purpose: AXI3 to AXI4 read protocol converter (pass-through)

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# AXI3 to AXI4 read converter
$CONVERTERS_ROOT/rtl/axi3_to_axi4_rd.sv
