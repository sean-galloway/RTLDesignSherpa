# Filelist for axi4_dwidth_converter_wr module
# Location: projects/components/converters/rtl/filelists/axi4_dwidth_converter_wr.f
# Purpose: AXI4 write data width converter (upsize/downsize with skid buffers)

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f

# Dependencies - Validated data-sizing primitives (wr uses both:
# DOWNSIZE direction → axi_data_dnsize; UPSIZE direction → axi_data_upsize).
$CONVERTERS_ROOT/rtl/axi_data_upsize.sv
$CONVERTERS_ROOT/rtl/axi_data_dnsize.sv

# AXI4 write data width converter
$CONVERTERS_ROOT/rtl/axi4_dwidth_converter_wr.sv
