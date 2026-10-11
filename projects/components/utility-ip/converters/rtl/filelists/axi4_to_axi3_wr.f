# Filelist for axi4_to_axi3_wr module
# Location: projects/components/utility-ip/converters/rtl/filelists/axi4_to_axi3_wr.f
# Purpose: AXI4 to AXI3 write protocol converter (pass-through + WID stamping)

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# AXI4 to AXI3 write converter
$CONVERTERS_ROOT/rtl/axi4_to_axi3_wr.sv
