# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Bridge RTL files (generated)
rtl/bridge_2x2_rw/bridge_2x2_rw_pkg.sv
rtl/bridge_2x2_rw/cpu_adapter.sv
rtl/bridge_2x2_rw/dma_adapter.sv
rtl/bridge_2x2_rw/bridge_2x2_rw.sv
rtl/bridge_2x2_rw/bridge_2x2_rw_xbar.sv
rtl/bridge_2x2_rw/ddr_adapter.sv
rtl/bridge_2x2_rw/sram_adapter.sv

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