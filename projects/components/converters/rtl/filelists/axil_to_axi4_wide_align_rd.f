# Filelist for axil_to_axi4_wide_align_rd module
# Location: projects/components/converters/rtl/filelists/axil_to_axi4_wide_align_rd.f
# Purpose: AXIL to wide AXI4 read alignment shim

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

$CONVERTERS_ROOT/rtl/axil_to_axi4_wide_align_rd.sv
