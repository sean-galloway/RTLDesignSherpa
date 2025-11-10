# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Bridge RTL files (generated)
generated/bridge_1x2_wr/bridge_1x2_wr_pkg.sv
generated/bridge_1x2_wr/cpu_adapter.sv
generated/bridge_1x2_wr/bridge_1x2_wr.sv
generated/bridge_1x2_wr/bridge_1x2_wr_xbar.sv

# AXI4 Wrapper modules (timing isolation)
$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd.sv

# GAXI skid buffers (used by wrappers and converters)
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# Width converters (for data width adaptation)
$REPO_ROOT/projects/components/converters/rtl/axi4_dwidth_converter_rd.sv
$REPO_ROOT/projects/components/converters/rtl/axi4_dwidth_converter_wr.sv