# Filelist for axi3_to_axi4 module
# Location: projects/components/utility-ip/converters/rtl/filelists/axi3_to_axi4.f
# Purpose: AXI3 to AXI4 converter (rd+wr top wrapper)

# Include directories

# Boundary reset synchronizer (block input reset is async-assert,
# synchronized internally; complete closure)
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Sub-blocks
-f $CONVERTERS_ROOT/rtl/filelists/axi3_to_axi4_rd.f
-f $CONVERTERS_ROOT/rtl/filelists/axi3_to_axi4_wr.f

$CONVERTERS_ROOT/rtl/axi3_to_axi4.sv
