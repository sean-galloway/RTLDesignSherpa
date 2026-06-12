# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Bridge RTL files (generated)
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_mix_b/bridge_mix_b_pkg.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_mix_b/cpu_axi4_adapter.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_mix_b/dma_axi4_adapter.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_mix_b/host_axil_adapter.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_mix_b/bridge_mix_b.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_mix_b/bridge_mix_b_xbar.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_mix_b/apb_periph_adapter.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_mix_b/ddr_adapter.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_mix_b/scratch_adapter.sv

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
$REPO_ROOT/rtl/amba/shared/cdc_2_phase_handshake.sv
$REPO_ROOT/rtl/amba/shared/cdc_4_phase_handshake.sv
$REPO_ROOT/projects/components/converters/rtl/axi4_to_apb_convert.sv
$REPO_ROOT/rtl/amba/apb/apb_master_stub.sv

# APB protocol converter (AXI4 to APB)
$REPO_ROOT/projects/components/converters/rtl/axi4_to_apb_shim.sv