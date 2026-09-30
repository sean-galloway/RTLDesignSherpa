# Filelist for scoria_core (new 3-layer controller)
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/includes/scoria_pkg.sv
# common / gaxi / amba
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/cdc/filelists/counter_johnson.f
-f $REPO_ROOT/rtl/common/filelists/find_first_set.f
-f $REPO_ROOT/rtl/common/filelists/find_last_set.f
-f $REPO_ROOT/rtl/common/filelists/leading_one_trailing_one.f
-f $REPO_ROOT/rtl/cdc/filelists/glitch_free_n_dff_arn.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/rtl/cdc/filelists/gaxi_fifo_async.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd.f
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_axi_burst_chopper.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_wr_splitter.sv
# pumice fubs
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_addr_mapper.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_wr_intake.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_rd_intake.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_wr_data_cam.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_rd_cmd_cam.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_rd_return_ring.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_bank_timer.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_bank_timers.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_global_timers.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_refresh_ctrl.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_init_sequencer.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_mode_register.sv
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_cmd_history_checker.f
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_page_policy.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_cmd_arbiter.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_dfi_cmd_formatter.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_dfi_cdc.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_dfi_cmd_path.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_dfi_wr_serializer.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_dfi_rd_aligner.sv
# macros
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/macro/scoria_axi4_ifc.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/macro/scoria_mem_cmd_scheduler.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/macro/scoria_dfi_layer.sv
# top
$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/top/scoria_core.sv
