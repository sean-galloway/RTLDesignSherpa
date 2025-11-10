# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Bridge RTL files (generated)
generated/bridge_1x3_rd/bridge_1x3_rd_pkg.sv
generated/bridge_1x3_rd/cpu_rd_adapter.sv
generated/bridge_1x3_rd/bridge_1x3_rd.sv
generated/bridge_1x3_rd/bridge_1x3_rd_xbar.sv
generated/bridge_1x3_rd/ddr_rd_adapter.sv
generated/bridge_1x3_rd/hbm_rd_adapter.sv
generated/bridge_1x3_rd/periph_rd_adapter.sv

# AXI4 Wrapper modules (timing isolation)
# Master adapters use axi4_slave_* (act as AXI slave to external master)
$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd.sv
# Slave adapters use axi4_master_* (act as AXI master to external slave)
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd.sv

# GAXI skid buffers (used by wrappers and converters)
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# Width converters (for data width adaptation)
$REPO_ROOT/projects/components/converters/rtl/axi4_dwidth_converter_rd.sv
$REPO_ROOT/projects/components/converters/rtl/axi4_dwidth_converter_wr.sv