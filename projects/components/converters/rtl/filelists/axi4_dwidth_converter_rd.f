# Filelist for axi4_dwidth_converter_rd module
# Location: projects/components/converters/rtl/filelists/axi4_dwidth_converter_rd.f
# Purpose: AXI4 read data width converter (upsize/downsize with skid buffers)

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Dependencies - Skid buffers for timing isolation
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# Dependencies - Validated data-sizing primitives (rd uses both:
# UPSIZE direction → axi_data_dnsize; DOWNSIZE direction → axi_data_upsize).
$CONVERTERS_ROOT/rtl/axi_data_upsize.sv
$CONVERTERS_ROOT/rtl/axi_data_dnsize.sv

# AXI4 read data width converter
$CONVERTERS_ROOT/rtl/axi4_dwidth_converter_rd.sv
