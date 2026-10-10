# Filelist for scoria_top (new controller top: pumice_core + PeakRDL CSR)
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/includes/scoria_pkg.sv
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/cdc/filelists/counter_johnson.f
-f $REPO_ROOT/rtl/common/filelists/find_first_set.f
-f $REPO_ROOT/rtl/common/filelists/find_last_set.f
-f $REPO_ROOT/rtl/common/filelists/leading_one_trailing_one.f
-f $REPO_ROOT/rtl/cdc/filelists/glitch_free_n_dff_arn.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_synchronizer.f
-f $REPO_ROOT/rtl/cdc/filelists/sync_pulse.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/rtl/cdc/filelists/gaxi_fifo_async.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd.f
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_axi_burst_chopper.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_wr_splitter.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_addr_mapper.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_wr_intake.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_rd_intake.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_wr_data_cam.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_rd_cmd_cam.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_rd_return_ring.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_bank_timer.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_bank_timers.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_global_timers.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_refresh_ctrl.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_zq_ctrl.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_wrlvl_ifc.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_init_sequencer.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_mode_register.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_page_policy.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_cmd_arbiter.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_dfi_cmd_formatter.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_dfi_cdc.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_dfi_cmd_path.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_dfi_wr_serializer.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_dfi_rd_aligner.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/macro/scoria_axi4_layer.sv
# pumice_mem_cmd_scheduler instantiates pumice_cmd_history_checker under
# CMD_HISTORY_EN. It is a GATED submodule -- absent at CMD_HISTORY_EN=0 -- so
# this filelist never carried it and the parameter could not be built from
# this top at all: Verilator stopped with MODMISSING. A parameter the design
# supports but the filelist cannot satisfy is a parameter nobody can use, and
# this one arms the command-spacing scoreboard (check 7 is the GLOBAL tRTW
# assertion), which is the instrument for TASK-007. Compiled always; with
# CMD_HISTORY_EN=0 it is simply not instantiated.
-f $REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_cmd_history_checker.f
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/macro/scoria_scheduler_layer.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/macro/scoria_dfi_layer.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/top/scoria_core.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/regs/generated/rtl/scoria_csr_pkg.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/regs/generated/rtl/scoria_csr.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/top/scoria_top.sv
