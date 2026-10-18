# Filelist for axi4_to_axi3_rd module
# Location: projects/components/utility-ip/converters/rtl/filelists/axi4_to_axi3_rd.f
# Purpose: AXI4 to AXI3 read protocol converter (pass-through)

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Queues and buffers (rtl/amba/gaxi)
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f

# AXI4 to AXI3 read converter
$CONVERTERS_ROOT/rtl/axi4_to_axi3_rd.sv
