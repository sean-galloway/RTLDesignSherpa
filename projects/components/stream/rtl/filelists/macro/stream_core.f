# Filelist for stream_core module (complete STREAM integration)
# Location: projects/components/stream/rtl/filelists/macro/stream_core.f
#
# Architecture: Complete STREAM DMA engine integration
# - scheduler_group_array (8 channels + descriptor fetch)
# - axi_read_engine (shared read master)
# - axi_write_engine (shared write master)
# - sram_controller (per-channel FIFOs)
# - perf_profiler (performance monitoring)
# - AXI skid buffers (descriptor, read, write)

# Include directories
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Package files
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# Dependencies - Common blocks
$REPO_ROOT/rtl/common/arbiter_priority_encoder.sv
$REPO_ROOT/rtl/common/arbiter_round_robin.sv
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/counter_freq_invariant.sv
$REPO_ROOT/rtl/common/counter_load_clear.sv
$REPO_ROOT/rtl/common/fifo_control.sv

# Dependencies - GAXI Components
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# Dependencies - AMBA Monitors (order matters - submodules before base)
$REPO_ROOT/rtl/amba/shared/axi_monitor_trans_mgr.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_timer.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_timeout.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_reporter.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_base.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_filtered.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd_mon.sv

# Dependencies - MonBus Infrastructure
$REPO_ROOT/rtl/amba/shared/monbus_arbiter.sv

# Dependencies - AXI skid buffers (from rtl/amba/axi4/)
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr.sv

# FUB Components
$STREAM_ROOT/rtl/fub/descriptor_engine.sv
$STREAM_ROOT/rtl/fub/scheduler.sv
$STREAM_ROOT/rtl/fub/stream_alloc_ctrl.sv
$STREAM_ROOT/rtl/fub/stream_latency_bridge.sv
$STREAM_ROOT/rtl/fub/axi_read_engine.sv
$STREAM_ROOT/rtl/fub/axi_write_engine.sv
$STREAM_ROOT/rtl/fub/sram_controller_unit.sv
$STREAM_ROOT/rtl/fub/sram_controller.sv
$STREAM_ROOT/rtl/fub/perf_profiler.sv

# Macro Components
$STREAM_ROOT/rtl/macro/scheduler_group.sv
$STREAM_ROOT/rtl/macro/scheduler_group_array.sv

# Top-level integration
$STREAM_ROOT/rtl/macro/stream_core.sv
