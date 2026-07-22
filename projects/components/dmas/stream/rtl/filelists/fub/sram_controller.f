# Filelist for sram_controller module
# Location: projects/components/dmas/stream/rtl/filelists/fub/sram_controller.f

# Include directories
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f

# Package files - STREAM only needs monitor_common_pkg (not the full monitor_pkg)
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# Stream components - allocation controller and latency bridge
$STREAM_ROOT/rtl/fub/stream_alloc_ctrl.sv
$STREAM_ROOT/rtl/fub/stream_drain_ctrl.sv
$STREAM_ROOT/rtl/fub/stream_latency_bridge.sv

# SRAM controller unit (single channel: alloc_ctrl + FIFO + latency bridge)
$STREAM_ROOT/rtl/fub/sram_controller_unit.sv

# SRAM controller top-level (must be last - instantiates units)
$STREAM_ROOT/rtl/fub/sram_controller.sv
