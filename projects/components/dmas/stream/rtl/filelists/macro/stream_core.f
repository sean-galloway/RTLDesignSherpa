# Filelist for stream_core module (complete STREAM integration)
# Location: projects/components/dmas/stream/rtl/filelists/macro/stream_core.f
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

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_wr_mon.f
-f $REPO_ROOT/rtl/amba/filelists/axi_bus_meter.f
-f $REPO_ROOT/rtl/amba/filelists/axi_perf_latency_hist.f

# Package files
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# Include macro-level components via -f (automatically pulls in dependencies)
-f $STREAM_ROOT/rtl/filelists/macro/scheduler_group_array.f

# Include FUB-level components via -f (automatically pulls in their dependencies)
-f $STREAM_ROOT/rtl/filelists/fub/axi_read_engine.f
-f $STREAM_ROOT/rtl/filelists/fub/axi_write_engine.f
-f $STREAM_ROOT/rtl/filelists/fub/sram_controller.f
-f $STREAM_ROOT/rtl/filelists/fub/perf_profiler.f

# Top-level integration (unique to this filelist)
$STREAM_ROOT/rtl/macro/stream_core.sv
