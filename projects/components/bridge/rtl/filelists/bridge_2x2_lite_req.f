# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Reset macro header (`ALWAYS_FF_RST / `RST_ASSERTED)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Monitor packages (must precede any module that references them)
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f

# Subtractive catch-all slave (unmapped-address terminator)
-f $REPO_ROOT/rtl/amba/filelists/axi4_subtractive_slave.f

# Bridge RTL files (generated)
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_2x2_lite_req/bridge_2x2_lite_req_pkg.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_2x2_lite_req/lite4_adapter.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_2x2_lite_req/lite5_adapter.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_2x2_lite_req/bridge_2x2_lite_req.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_2x2_lite_req/bridge_2x2_lite_req_xbar.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_2x2_lite_req/mem_adapter.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_2x2_lite_req/regs_adapter.sv
$REPO_ROOT/projects/components/bridge/rtl/generated/bridge_2x2_lite_req/subtractive_adapter.sv

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

# Per-ID response tracking (bridge_cam): enable_ooo slaves, and every AXI
# slave of a multi-master fabric, whose IDs are {master index, id} (BRIDGE-015/016)
-f $REPO_ROOT/projects/components/bridge/rtl/filelists_static/bridge_cam.f

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

# AXI4-to-AXI5-Lite converter dependencies (protocol=axil5 slaves)
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_to_axil5_rd.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_to_axil5_wr.f