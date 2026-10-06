# Filelist for andesite_axi4_layer
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/includes/andesite_pkg.sv
# common / gaxi
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
# AXI slave protocol
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd.f
# pumice FSM-free splitters + aggregators
$REPO_ROOT/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_axi_burst_chopper.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_wr_splitter.sv
# pumice fubs
$REPO_ROOT/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_addr_mapper.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_wr_intake.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_rd_intake.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_wr_data_cam.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_rd_cmd_cam.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_rd_return_ring.sv
# wrapper
$REPO_ROOT/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/macro/andesite_axi4_layer.sv
