# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Bridge RTL files (generated)
generated/bridge_1x5_rd/bridge_1x5_rd_pkg.sv
generated/bridge_1x5_rd/cpu_rd_adapter.sv
generated/bridge_1x5_rd/bridge_1x5_rd.sv
generated/bridge_1x5_rd/bridge_1x5_rd_xbar.sv
generated/bridge_1x5_rd/apb_periph_adapter.sv
generated/bridge_1x5_rd/axil_periph_adapter.sv
generated/bridge_1x5_rd/ddr_rd_adapter.sv
generated/bridge_1x5_rd/hbm_rd_adapter.sv
generated/bridge_1x5_rd/periph_rd_adapter.sv

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

# APB protocol converter dependencies (in dependency order)
# Common dependencies first
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv

# AMBA shared modules
$REPO_ROOT/rtl/amba/shared/axi_gen_addr.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv

# AXI4 stubs
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_wr_stub.sv
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_rd_stub.sv
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_stub.sv

# APB modules
$REPO_ROOT/rtl/amba/apb/apb_master.sv
$REPO_ROOT/rtl/amba/shared/cdc_handshake.sv
$REPO_ROOT/projects/components/converters/rtl/axi4_to_apb_convert.sv
$REPO_ROOT/rtl/amba/apb/apb_master_stub.sv

# APB protocol converter (AXI4 to APB)
$REPO_ROOT/projects/components/converters/rtl/axi4_to_apb_shim.sv

# AXI4-Lite protocol converter dependencies
$REPO_ROOT/projects/components/converters/rtl/axi4_to_axil4_rd.sv
$REPO_ROOT/projects/components/converters/rtl/axi4_to_axil4_wr.sv