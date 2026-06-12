# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Bridge RTL files (generated)
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_1x2_rd/bridge_1x2_rd_pkg.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_1x2_rd/cpu_rd_adapter.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_1x2_rd/bridge_1x2_rd.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_1x2_rd/bridge_1x2_rd_xbar.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_1x2_rd/ddr_rd_adapter.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_1x2_rd/sram_rd_adapter.sv

# AXI4 Wrapper modules (timing isolation)
# Master adapters use axi4_slave_* (act as AXI slave to external master)
$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd.sv
# Slave adapters use axi4_master_* (act as AXI master to external slave)
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd.sv

# GAXI skid buffers (used by wrappers and converters)
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# Width converters (for data width adaptation).
# axi_data_{upsize,dnsize} are validated primitives used by the
# axi4_dwidth_converter_{rd,wr} wrappers for the W/R data path.
$REPO_ROOT/projects/components/converters/rtl/axi_data_upsize.sv
$REPO_ROOT/projects/components/converters/rtl/axi_data_dnsize.sv
$REPO_ROOT/projects/components/converters/rtl/axi4_dwidth_converter_rd.sv
$REPO_ROOT/projects/components/converters/rtl/axi4_dwidth_converter_wr.sv
$REPO_ROOT/projects/components/converters/rtl/axil_to_axi4_wide_align_wr.sv
$REPO_ROOT/projects/components/converters/rtl/axil_to_axi4_wide_align_rd.sv