# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Bridge RTL files (generated)
generated/bridge_4x4_rw/bridge_4x4_rw_pkg.sv
generated/bridge_4x4_rw/cpu_master_adapter.sv
generated/bridge_4x4_rw/dma0_master_adapter.sv
generated/bridge_4x4_rw/dma1_master_adapter.sv
generated/bridge_4x4_rw/gpu_master_adapter.sv
generated/bridge_4x4_rw/bridge_4x4_rw.sv
generated/bridge_4x4_rw/bridge_4x4_rw_xbar.sv

# AXI4 Wrapper modules (timing isolation)
$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd.sv

# GAXI skid buffers (used by wrappers and converters)
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# Width converters (for data width adaptation)
$REPO_ROOT/projects/components/converters/rtl/axi4_dwidth_converter_rd.sv
$REPO_ROOT/projects/components/converters/rtl/axi4_dwidth_converter_wr.sv