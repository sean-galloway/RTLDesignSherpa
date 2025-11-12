# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Bridge RTL files (generated)
generated/bridge_5x3_channels/bridge_5x3_channels_pkg.sv
generated/bridge_5x3_channels/cpu_master_adapter.sv
generated/bridge_5x3_channels/descr_wr_master_adapter.sv
generated/bridge_5x3_channels/sink_wr_master_adapter.sv
generated/bridge_5x3_channels/src_rd_master_adapter.sv
generated/bridge_5x3_channels/stream_master_adapter.sv
generated/bridge_5x3_channels/bridge_5x3_channels.sv
generated/bridge_5x3_channels/bridge_5x3_channels_xbar.sv
generated/bridge_5x3_channels/apb_periph_adapter.sv
generated/bridge_5x3_channels/ddr_controller_adapter.sv
generated/bridge_5x3_channels/sram_buffer_adapter.sv

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