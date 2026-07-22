# Filelist for scheduler module
# Location: projects/components/dmas/stream/rtl/filelists/fub/scheduler.f

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

# Package files
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# TASK-101 run-base address generator dependencies (USE_ROW_COL_MAJOR_ADDRESSING)
$REPO_ROOT/projects/components/misc/rtl/dma_address_gen.sv
$STREAM_ROOT/rtl/fub/stream_run_addr_gen.sv

# Scheduler module
$STREAM_ROOT/rtl/fub/scheduler.sv
