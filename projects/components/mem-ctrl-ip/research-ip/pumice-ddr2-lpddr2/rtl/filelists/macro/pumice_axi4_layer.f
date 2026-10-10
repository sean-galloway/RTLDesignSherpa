# Filelist for pumice_axi4_layer
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/includes/mc_common_pkg.f
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/includes/pumice_pkg.sv
# common / gaxi
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
# AXI slave protocol
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd.f
# pumice FSM-free splitters + aggregators
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_axi_burst_chopper.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_wr_splitter.f
# pumice fubs
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/fub/addr_mapper.sv
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_wr_intake.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_rd_intake.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_wr_data_cam.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_rd_cmd_cam.f
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/fub/pumice_rd_return_ring.sv
# wrapper
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/macro/pumice_axi4_layer.sv
