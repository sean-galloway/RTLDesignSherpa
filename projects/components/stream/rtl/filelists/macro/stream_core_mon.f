# Filelist for stream_core_mon module (STREAM with integrated AXI monitors)
# Location: projects/components/stream/rtl/filelists/macro/stream_core_mon.f
#
# Architecture: Complete STREAM DMA engine with AXI4 monitoring wrappers
# - scheduler_group_array (8 channels + descriptor fetch)
# - axi_read_engine → axi4_master_rd_mon (read master with monitoring)
# - axi_write_engine → axi4_master_wr_mon (write master with monitoring)
# - sram_controller (per-channel FIFOs)
# - perf_profiler (performance monitoring)
# - MonBus outputs from read/write AXI monitors

# Include directories
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Package files
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# Additional dependencies not covered by FUB-level includes
# GAXI skid buffer (used by stream_core_mon for AXI interfaces)
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# Counter modules used by stream_core_mon directly
$REPO_ROOT/rtl/common/counter_freq_invariant.sv
$REPO_ROOT/rtl/common/counter_load_clear.sv

# AMBA Monitors - Use -f to include complete monitor infrastructure
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd_mon.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_wr_mon.f

# Include macro-level components via -f (automatically pulls in dependencies)
-f $STREAM_ROOT/rtl/filelists/macro/scheduler_group_array.f

# Include FUB-level components via -f (automatically pulls in their dependencies)
-f $STREAM_ROOT/rtl/filelists/fub/axi_read_engine.f
-f $STREAM_ROOT/rtl/filelists/fub/axi_write_engine.f
-f $STREAM_ROOT/rtl/filelists/fub/sram_controller.f
-f $STREAM_ROOT/rtl/filelists/fub/perf_profiler.f

# Top-level integration with monitoring (unique to this filelist)
$STREAM_ROOT/rtl/macro/stream_core_mon.sv
