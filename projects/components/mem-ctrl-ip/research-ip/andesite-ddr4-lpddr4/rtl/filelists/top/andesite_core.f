# Filelist for andesite_core (new 4-layer controller)
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/includes/mc_common_pkg.f
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/includes/andesite_pkg.sv
# common / gaxi / amba
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
# pumice FSM-free splitters + aggregators
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_axi_burst_chopper.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_wr_splitter.f
# pumice fubs
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_addr_mapper.sv
# intakes + return ring are inside mc_axi4_layer.f; CAMs inside mc_storage_layer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_wr_intake.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_rd_intake.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_bank_timer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_bank_timers.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_global_timers.f
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_refresh_ctrl.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_zq_mpc_lpddr4.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_zq_ctrl.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_wrlvl_ifc.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_rdlvl_ifc.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_ca_train_ifc.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_init_sequencer.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_mode_register.sv
-f $REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/filelists/fub/andesite_cmd_history_checker.f
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_page_policy.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_cmd_arbiter.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_dfi_cmd_formatter.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_dfi_cdc.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_dfi_cmd_path.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_dfi_wr_serializer.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_dfi_rd_aligner.sv
# macros
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_axi4_layer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_storage_layer.f
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/macro/andesite_scheduler_layer.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/macro/andesite_training_layer.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/macro/andesite_dfi_layer.sv
# top
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/top/andesite_core.sv
