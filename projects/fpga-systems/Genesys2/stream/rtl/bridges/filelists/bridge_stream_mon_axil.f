# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Bridge RTL files (generated)
$REPO_ROOT/projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/bridge_stream_mon_axil/bridge_stream_mon_axil_pkg.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/bridge_stream_mon_axil/host_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/bridge_stream_mon_axil/monbus_wr_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/bridge_stream_mon_axil/slave_monbus_wr_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/bridge_stream_mon_axil/stream_desc_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/bridge_stream_mon_axil/bridge_stream_mon_axil.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/bridge_stream_mon_axil/bridge_stream_mon_axil_xbar.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/bridge_stream_mon_axil/desc_ram_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/bridge_stream_mon_axil/dma_axil_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/bridge_stream_mon_axil/harness_csr_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/bridge_stream_mon_axil/obs_apb_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/bridge_stream_mon_axil/slave_err_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/bridge_stream_mon_axil/slave_tally_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/bridge_stream_mon_axil/slave_tally_cfg_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/bridge_stream_mon_axil/slvmon_apb_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/bridge_stream_mon_axil/stream_apb_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/bridge_stream_mon_axil/stream_err_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/bridge_stream_mon_axil/stream_tally_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/bridge_stream_mon_axil/stream_tally_cfg_adapter.sv

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

# APB protocol converter (AXI4 to APB).
#
# The converters component owns its own closure: the shim + convert
# core, the CDC handshakes, the APB master/stub, the AXI4 slave stubs,
# axi_gen_addr and both gaxi FIFOs. Hand-listing those here is how the
# shim's newer gaxi_fifo_async CDC dependency went missing.
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_to_apb_shim.f

# AXI4-Lite protocol converter dependencies.
# -f the converters filelists; do not hand-list its sources.
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_to_axil4_rd.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_to_axil4_wr.f