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

# Additional dependencies not covered by FUB-level includes
# GAXI skid buffer (used by stream_core for AXI interfaces)
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# Counter modules used by stream_core directly
$REPO_ROOT/rtl/common/counter_freq_invariant.sv
$REPO_ROOT/rtl/common/counter_load_clear.sv

# AXI skid buffer wrappers (used by stream_core for interface buffering)
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr.sv

# Include macro-level components via -f (automatically pulls in dependencies)
-f $STREAM_ROOT/rtl/filelists/macro/scheduler_group_array.f

# Include FUB-level components via -f (automatically pulls in their dependencies)
-f $STREAM_ROOT/rtl/filelists/fub/axi_read_engine.f
-f $STREAM_ROOT/rtl/filelists/fub/axi_write_engine.f
-f $STREAM_ROOT/rtl/filelists/fub/sram_controller.f
-f $STREAM_ROOT/rtl/filelists/fub/perf_profiler.f

# Top-level integration (unique to this filelist)
$STREAM_ROOT/rtl/macro/stream_core.sv
