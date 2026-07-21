# Filelist for pumice_core (new 3-layer controller)
+incdir+$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/includes/pumice_pkg.sv
# common / gaxi / amba
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/counter_johnson.f
-f $REPO_ROOT/rtl/common/filelists/find_first_set.f
-f $REPO_ROOT/rtl/common/filelists/find_last_set.f
-f $REPO_ROOT/rtl/common/filelists/leading_one_trailing_one.f
-f $REPO_ROOT/rtl/common/filelists/glitch_free_n_dff_arn.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_async.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd.f
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/pumice_axi_burst_chopper.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/pumice_wr_splitter.sv
# pumice fubs
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/addr_mapper.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/pumice_wr_intake.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/pumice_rd_intake.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/pumice_wr_data_cam.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/pumice_rd_cmd_cam.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/bank_timer.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/pumice_bank_timers.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/global_timers.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/refresh_ctrl.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/init_sequencer.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/mode_register.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/pumice_cmd_arbiter.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/dfi_cmd_formatter.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/pumice_dfi_cdc.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/pumice_dfi_cmd_path.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/pumice_dfi_wr_serializer.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/pumice_dfi_rd_aligner.sv
# macros
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/macro/pumice_axi4_ifc.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/macro/pumice_mem_cmd_scheduler.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/macro/pumice_dfi_layer.sv
# top
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/top/pumice_core.sv
