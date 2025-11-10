# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Bridge RTL files (generated)
generated/bridge_1x2_rd/bridge_1x2_rd_pkg.sv
generated/bridge_1x2_rd/cpu_master_adapter.sv
generated/bridge_1x2_rd/bridge_1x2_rd.sv
generated/bridge_1x2_rd/bridge_1x2_rd_xbar.sv

# AXI4 Wrapper modules (timing isolation)
$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd.sv

# GAXI skid buffers (used by wrappers and converters)
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# Width converters (for data width adaptation)
$REPO_ROOT/projects/components/converters/rtl/axi4_dwidth_converter_rd.sv
$REPO_ROOT/projects/components/converters/rtl/axi4_dwidth_converter_wr.sv