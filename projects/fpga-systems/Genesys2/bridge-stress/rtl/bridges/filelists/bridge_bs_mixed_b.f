# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Reset macro header (`ALWAYS_FF_RST / `RST_ASSERTED)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Monitor packages (must precede any module that references them)
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f

# Subtractive catch-all slave (unmapped-address terminator)
-f $REPO_ROOT/rtl/amba/filelists/axi4_subtractive_slave.f

# Bridge RTL files (generated)
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/bridges/generated/bridge_bs_mixed_b/bridge_bs_mixed_b_pkg.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/bridges/generated/bridge_bs_mixed_b/cpu_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/bridges/generated/bridge_bs_mixed_b/l4m_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/bridges/generated/bridge_bs_mixed_b/l5m_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/bridges/generated/bridge_bs_mixed_b/p4m_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/bridges/generated/bridge_bs_mixed_b/p5m_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/bridges/generated/bridge_bs_mixed_b/wbm_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/bridges/generated/bridge_bs_mixed_b/bridge_bs_mixed_b.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/bridges/generated/bridge_bs_mixed_b/bridge_bs_mixed_b_xbar.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/bridges/generated/bridge_bs_mixed_b/l4s_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/bridges/generated/bridge_bs_mixed_b/l5s_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/bridges/generated/bridge_bs_mixed_b/mem_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/bridges/generated/bridge_bs_mixed_b/p4s_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/bridges/generated/bridge_bs_mixed_b/p5s_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/bridges/generated/bridge_bs_mixed_b/subtractive_adapter.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/bridge-stress/rtl/bridges/generated/bridge_bs_mixed_b/wbs_adapter.sv

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

# APB4 requester front end (masters with protocol=apb)
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/apb4_to_axi4.f

# APB5 requester front end (masters with protocol=apb5)
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/apb5_to_axi4.f

# Wishbone B4 requester front end (masters with protocol=wb4, bridge TASK-008 (was BRIDGE-019))
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/wb4_to_axi4.f

# Rate-matching buffers on upsized paths into shared slaves (bridge W2)
-f $REPO_ROOT/projects/components/fabric-gen-ip/bridge/rtl/filelists_static/bridge_wr_rate_buf.f

# Transaction-ID remap tables in the master adapters (bridge_id_remap)
-f $REPO_ROOT/projects/components/fabric-gen-ip/bridge/rtl/filelists_static/bridge_id_remap.f

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
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi_data_upsize.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi_data_dnsize.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi4_dwidth_converter_rd.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi4_dwidth_converter_wr.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axil_to_axi4_wide_align_wr.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axil_to_axi4_wide_align_rd.f

# APB protocol converter (AXI4 to APB).
#
# The converters component owns its own closure: the shim + convert
# core, the CDC handshakes, the APB master/stub, the AXI4 slave stubs,
# axi_gen_addr and both gaxi FIFOs. Hand-listing those here is how the
# shim's newer gaxi_fifo_async CDC dependency went missing.
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi4_to_apb4_shim.f

# AXI4-to-APB5 converter shim (protocol=apb5 slaves)
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi4_to_apb5_shim.f

# AXI4-Lite protocol converter dependencies.
# -f the converters filelists; do not hand-list its sources.
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi4_to_axil4_rd.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi4_to_axil4_wr.f

# AXI4-to-AXI5-Lite converter dependencies (protocol=axil5 slaves)
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi4_to_axil5_rd.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi4_to_axil5_wr.f

# AXI4-to-Wishbone B4 converter (protocol=wb4 slaves)
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi4_to_wb4.f