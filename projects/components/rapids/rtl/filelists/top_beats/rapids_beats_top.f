# Filelist for rapids_beats_top (RAPIDS beats DMA top-level)
# Location: projects/components/rapids/rtl/filelists/top_beats/rapids_beats_top.f
#
# Self-contained, deduplicated union of:
#   - rapids_core_beats (scheduler array + sink/source data paths)
#   - axi4_master_rd_mon + axi4_master_wr_mon + monbus_arbiter (USE_AXI_MONITORS)
#   - APB -> reg chain: apb_slave, cmdrsp_router, apbtodescr, peakrdl_to_cmdrsp
#   - rapids_regs (PeakRDL) + rapids_config_block + rapids_beats_top

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/rtl/common/includes
+incdir+$REPO_ROOT/projects/components/rapids/rtl/includes
+incdir+$REPO_ROOT/projects/components/stream/rtl/includes

# ---- Core + AXI monitor union (deduplicated, packages first) ----
$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba4_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba5_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_arbiter_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$REPO_ROOT/projects/components/rapids/rtl/includes/rapids_pkg.sv
$REPO_ROOT/projects/components/rapids/rtl/fub_beats/scheduler_beats.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/common/fifo_sync.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/projects/components/rapids/rtl/fub_beats/descriptor_engine_beats.sv
$REPO_ROOT/rtl/amba/shared/monbus_arbiter.sv
$REPO_ROOT/rtl/common/arbiter_round_robin.sv
$REPO_ROOT/rtl/common/arbiter_priority_encoder.sv
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/scheduler_group_beats.sv
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/common/counter_load_clear.sv
$REPO_ROOT/rtl/common/counter_freq_invariant.sv
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh
$REPO_ROOT/rtl/amba/shared/monitor_trans_cam.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_trans_mgr.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_timer.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_timeout.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_reporter_error.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_reporter_timeout.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_reporter_compl.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_reporter_threshold.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_reporter_perf.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_reporter_debug.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_reporter.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_base.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_filtered.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd_mon.sv
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/scheduler_group_array_beats.sv
$REPO_ROOT/projects/components/rapids/rtl/fub_beats/alloc_ctrl_beats.sv
$REPO_ROOT/projects/components/rapids/rtl/fub_beats/drain_ctrl_beats.sv
$REPO_ROOT/projects/components/rapids/rtl/fub_beats/latency_bridge_beats.sv
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/snk_sram_controller_unit_beats.sv
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/snk_sram_controller_beats.sv
$REPO_ROOT/projects/components/rapids/rtl/fub_beats/axi_write_engine_beats.sv
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/snk_data_path_beats.sv
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/src_sram_controller_unit_beats.sv
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/src_sram_controller_beats.sv
$REPO_ROOT/projects/components/rapids/rtl/fub_beats/axi_read_engine_beats.sv
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/src_data_path_beats.sv
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/rapids_core_beats.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr_mon.sv

# ---- MonBus AXI-Lite group (USE_AXI_MONITORS=1) ----
# The combined 128-bit MonBus stream is routed through monbus_axil_axil_group
# (AXI-Lite err-drain slave + bulk-capture master + IRQ), mirroring
# stream_top_ch8. AXIL leaves + shared group core (monbus_group.f). The
# monitor_*_pkg packages, gaxi_skid_buffer/gaxi_fifo_sync/fifo_control/
# counter_bin leaves and +incdirs are already listed above.
$REPO_ROOT/rtl/amba/axil4/axil4_slave_rd.sv
$REPO_ROOT/rtl/amba/axil4/axil4_master_wr.sv
-f $REPO_ROOT/rtl/amba/filelists/monbus_group.f
$REPO_ROOT/rtl/amba/shared/monbus_axil_axil_group.sv

# ---- APB -> register chain ----
$REPO_ROOT/projects/components/stream/rtl/includes/stream_pkg.sv
$REPO_ROOT/rtl/amba/apb/apb_slave.sv
$REPO_ROOT/projects/components/stream/rtl/top/cmdrsp_router.sv
$REPO_ROOT/projects/components/stream/rtl/fub/apbtodescr.sv
$REPO_ROOT/projects/components/converters/rtl/peakrdl_to_cmdrsp.sv

# ---- PeakRDL register file ----
$REPO_ROOT/projects/components/rapids/regs/generated/rtl/rapids_regs_pkg.sv
$REPO_ROOT/projects/components/rapids/regs/generated/rtl/rapids_regs.sv

# ---- Config mapping + top ----
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/rapids_config_block.sv
$REPO_ROOT/projects/components/rapids/rtl/top_beats/rapids_beats_top.sv
