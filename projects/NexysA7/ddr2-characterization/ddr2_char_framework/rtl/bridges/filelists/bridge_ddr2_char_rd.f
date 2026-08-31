# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Bridge RTL files (generated)
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/bridges/generated/bridge_ddr2_char_rd/bridge_ddr2_char_rd_pkg.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/bridges/generated/bridge_ddr2_char_rd/rdgen0_adapter.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/bridges/generated/bridge_ddr2_char_rd/rdgen1_adapter.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/bridges/generated/bridge_ddr2_char_rd/rdgen2_adapter.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/bridges/generated/bridge_ddr2_char_rd/rdgen3_adapter.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/bridges/generated/bridge_ddr2_char_rd/bridge_ddr2_char_rd.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/bridges/generated/bridge_ddr2_char_rd/bridge_ddr2_char_rd_xbar.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/bridges/generated/bridge_ddr2_char_rd/pumice_rd_adapter.sv

# AXI4 Wrapper modules (timing isolation)
#
# Pulled in via each component's OWN filelist rather than by hand-listing
# individual rtl/amba or rtl/common sources. A consumer that hand-lists a
# component's files has to track that component's internal dependencies,
# and it silently rots when they change. Each filelist below declares its
# own complete closure (packages + rtl/common deps + sub-blocks).
# Master adapters use axi4_slave_* (act as AXI slave to external master)
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd.f
# Slave adapters use axi4_master_* (act as AXI master to external slave)
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd.f

# GAXI skid buffers (used by wrappers and converters)
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f

# Width converters (for data width adaptation).
# axi_data_{upsize,dnsize} are validated primitives used by the
# axi4_dwidth_converter_{rd,wr} wrappers for the W/R data path.
#
# -f the converters component's own filelists rather than naming its
# .sv files: a consumer that hand-lists another component's sources has
# to track that component's internal dependencies, and rots silently
# when they change.
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi_data_upsize.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi_data_dnsize.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_dwidth_converter_rd.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_dwidth_converter_wr.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axil_to_axi4_wide_align_wr.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axil_to_axi4_wide_align_rd.f