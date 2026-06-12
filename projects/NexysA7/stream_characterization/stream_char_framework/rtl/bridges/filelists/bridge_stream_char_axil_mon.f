# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Monitor packages (must precede any module that references them)
$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba4_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba5_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_arbiter_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv

# Bridge RTL files (generated)
$REPO_ROOT/projects/NexysA7/stream_characterization/stream_char_framework/rtl/bridges/generated/bridge_stream_char_axil_mon/bridge_stream_char_axil_mon_pkg.sv
$REPO_ROOT/projects/NexysA7/stream_characterization/stream_char_framework/rtl/bridges/generated/bridge_stream_char_axil_mon/bridge_stream_char_axil_mon_cfg_pkg.sv
$REPO_ROOT/projects/NexysA7/stream_characterization/stream_char_framework/rtl/bridges/generated/bridge_stream_char_axil_mon/bridge_stream_char_axil_mon_cfg.sv
$REPO_ROOT/projects/NexysA7/stream_characterization/stream_char_framework/rtl/bridges/generated/bridge_stream_char_axil_mon/host_adapter.sv
$REPO_ROOT/projects/NexysA7/stream_characterization/stream_char_framework/rtl/bridges/generated/bridge_stream_char_axil_mon/monbus_wr_adapter.sv
$REPO_ROOT/projects/NexysA7/stream_characterization/stream_char_framework/rtl/bridges/generated/bridge_stream_char_axil_mon/stream_desc_adapter.sv
$REPO_ROOT/projects/NexysA7/stream_characterization/stream_char_framework/rtl/bridges/generated/bridge_stream_char_axil_mon/bridge_stream_char_axil_mon.sv
$REPO_ROOT/projects/NexysA7/stream_characterization/stream_char_framework/rtl/bridges/generated/bridge_stream_char_axil_mon/bridge_stream_char_axil_mon_xbar.sv
$REPO_ROOT/projects/NexysA7/stream_characterization/stream_char_framework/rtl/bridges/generated/bridge_stream_char_axil_mon/debug_sram_adapter.sv
$REPO_ROOT/projects/NexysA7/stream_characterization/stream_char_framework/rtl/bridges/generated/bridge_stream_char_axil_mon/desc_ram_adapter.sv
$REPO_ROOT/projects/NexysA7/stream_characterization/stream_char_framework/rtl/bridges/generated/bridge_stream_char_axil_mon/dma_axil_adapter.sv
$REPO_ROOT/projects/NexysA7/stream_characterization/stream_char_framework/rtl/bridges/generated/bridge_stream_char_axil_mon/harness_csr_adapter.sv
$REPO_ROOT/projects/NexysA7/stream_characterization/stream_char_framework/rtl/bridges/generated/bridge_stream_char_axil_mon/stream_apb_adapter.sv
$REPO_ROOT/projects/NexysA7/stream_characterization/stream_char_framework/rtl/bridges/generated/bridge_stream_char_axil_mon/stream_err_adapter.sv

# AXI4 Wrapper modules (timing isolation)
# Master adapters use axi4_slave_* (act as AXI slave to external master)
$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd.sv
# Slave adapters use axi4_master_* (act as AXI master to external slave)
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd.sv

# GAXI skid buffers (used by wrappers and converters)
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# Width converters (for data width adaptation).
# axi_data_{upsize,dnsize} are validated primitives used by the
# axi4_dwidth_converter_{rd,wr} wrappers for the W/R data path.
$REPO_ROOT/projects/components/converters/rtl/axi_data_upsize.sv
$REPO_ROOT/projects/components/converters/rtl/axi_data_dnsize.sv
$REPO_ROOT/projects/components/converters/rtl/axi4_dwidth_converter_rd.sv
$REPO_ROOT/projects/components/converters/rtl/axi4_dwidth_converter_wr.sv
$REPO_ROOT/projects/components/converters/rtl/axil_to_axi4_wide_align_wr.sv
$REPO_ROOT/projects/components/converters/rtl/axil_to_axi4_wide_align_rd.sv

# APB protocol converter dependencies (in dependency order)
# Common dependencies first
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv

# AMBA shared modules
$REPO_ROOT/rtl/amba/shared/axi_gen_addr.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv

# AXI4 stubs
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_wr_stub.sv
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_rd_stub.sv
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_stub.sv

# APB modules
$REPO_ROOT/rtl/amba/apb/apb_master.sv
$REPO_ROOT/rtl/amba/shared/cdc_2_phase_handshake.sv
$REPO_ROOT/rtl/amba/shared/cdc_4_phase_handshake.sv
$REPO_ROOT/projects/components/converters/rtl/axi4_to_apb_convert.sv
$REPO_ROOT/rtl/amba/apb/apb_master_stub.sv

# APB protocol converter (AXI4 to APB)
$REPO_ROOT/projects/components/converters/rtl/axi4_to_apb_shim.sv

# AXI4-Lite protocol converter dependencies
$REPO_ROOT/projects/components/converters/rtl/axi4_to_axil4_rd.sv
$REPO_ROOT/projects/components/converters/rtl/axi4_to_axil4_wr.sv

# Monitor-aggregation infrastructure (variant=mon)
# Header files with macros (already compiled if AMBA pkg path included)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh
# Common arbitration primitives (used by axi_monitor_*)
$REPO_ROOT/rtl/common/arbiter_priority_encoder.sv
$REPO_ROOT/rtl/common/arbiter_round_robin.sv
# Common counters & FIFO control (used by gaxi_fifo_sync + axi_monitor_timer)
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/counter_load_clear.sv
$REPO_ROOT/rtl/common/counter_freq_invariant.sv
$REPO_ROOT/rtl/common/fifo_control.sv
# axi_monitor_* shared infrastructure (order matters)
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
# _mon wrapper variants (instantiated by adapters when use_monitor=true)
$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr_mon.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd_mon.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr_mon.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd_mon.sv
# Monbus arbiter (always present in mon variant)
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/shared/monbus_arbiter.sv
# Monbus group (monbus_axil_axil_group) + its leaf skids + core
$REPO_ROOT/rtl/amba/axil4/axil4_slave_rd.sv
$REPO_ROOT/rtl/amba/axil4/axil4_master_wr.sv
$REPO_ROOT/rtl/amba/shared/monbus_cam.sv
$REPO_ROOT/rtl/amba/shared/monbus_compressor.sv
$REPO_ROOT/rtl/amba/shared/monbus_group_core.sv
$REPO_ROOT/rtl/amba/shared/monbus_axil_axil_group.sv