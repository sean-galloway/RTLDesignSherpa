# fb_harness, everything but the fabric under test. A leg's harness filelist is
# this plus that leg's fb_data_fabric filelist (fb_harness_<leg>.f).
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$STREAM_ROOT/regs/generated/rtl
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
# STREAM in its Genesys 2 configuration (the package the STREAM build uses)
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/stream_cfg_pkg.sv
-f $STREAM_ROOT/rtl/filelists/top/stream_top_ch8.f
# The STREAM harness's CSR block, unchanged (BUILD_*, timer, CRCs, CTRL)
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/regs/generated/rtl/harness_csr_regs_top_pkg.sv
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/regs/generated/rtl/harness_csr_regs_top.sv
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/harness_csr.sv
# Host link and control-side plumbing
-f $CONVERTERS_ROOT/rtl/filelists/uart_axil_bridge.f
-f $REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/bridges/filelists/bridge_fb_cfg.f
# Descriptor path: 256 -> 128 outside the fabric, descriptor RAM at S1
-f $CONVERTERS_ROOT/rtl/filelists/axi4_dwidth_converter_rd.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axi4_axi4.f
# Endpoints (S2/S3) and the run timer
-f $REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/filelists/fb_endpoints.f
-f $MISC_ROOT/rtl/filelists/char_run_timer.f
-f $MISC_ROOT/rtl/filelists/axi4_intf_master_observer.f
$REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/fb_axil_wr_sink.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/fb_apb_stub.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/fb_axi4_rd_stub.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/fb_harness.sv
