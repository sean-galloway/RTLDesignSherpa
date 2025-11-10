# Filelist for axi4_dwidth_converter_wr module
# Location: projects/components/converters/rtl/filelists/axi4_dwidth_converter_wr.f
# Purpose: AXI4 write data width converter (upsize/downsize with skid buffers)

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Dependencies - Skid buffers for timing isolation
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# AXI4 write data width converter
$CONVERTERS_ROOT/rtl/axi4_dwidth_converter_wr.sv
