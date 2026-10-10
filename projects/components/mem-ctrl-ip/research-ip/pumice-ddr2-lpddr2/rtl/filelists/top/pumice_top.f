# Filelist for pumice_top (new controller top: pumice_core + PeakRDL CSR)
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/includes/mc_common_pkg.f
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/includes/pumice_pkg.sv
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
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_axi_burst_chopper.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_wr_splitter.f
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/fub/addr_mapper.sv
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_wr_intake.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_rd_intake.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_wr_data_cam.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_rd_cmd_cam.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_rd_return_ring.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_bank_timer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_bank_timers.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_global_timers.f
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/fub/refresh_ctrl.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/fub/init_sequencer.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/fub/mode_register.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/fub/pumice_page_policy.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/fub/pumice_cmd_arbiter.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/fub/dfi_cmd_formatter.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/fub/pumice_dfi_cdc.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/fub/pumice_dfi_cmd_path.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/fub/pumice_dfi_wr_serializer.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/fub/pumice_dfi_rd_aligner.sv
# training layer + CDC helpers
-f $REPO_ROOT/rtl/cdc/filelists/sync_pulse.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_synchronizer.f
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/fub/pumice_zq_ctrl.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/fub/pumice_lp_cal.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/macro/pumice_training_layer.sv
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_axi4_layer.f
# pumice_scheduler_layer instantiates pumice_cmd_history_checker under
# CMD_HISTORY_EN. It is a GATED submodule -- absent at CMD_HISTORY_EN=0 -- so
# this filelist never carried it and the parameter could not be built from
# this top at all: Verilator stopped with MODMISSING. A parameter the design
# supports but the filelist cannot satisfy is a parameter nobody can use, and
# this one arms the command-spacing scoreboard (check 7 is the GLOBAL tRTW
# assertion), which is the instrument for TASK-007. Compiled always; with
# CMD_HISTORY_EN=0 it is simply not instantiated.
-f $REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/filelists/fub/pumice_cmd_history_checker.f
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/macro/pumice_scheduler_layer.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/macro/pumice_dfi_layer.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/top/pumice_core.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/regs/generated/rtl/pumice_csr_pkg.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/regs/generated/rtl/pumice_csr.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/top/pumice_top.sv
