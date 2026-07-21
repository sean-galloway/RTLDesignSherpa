# Filelist for axi_write_engine module
# Location: projects/components/dmas/stream/rtl/filelists/fub/axi_write_engine.f

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
-f $REPO_ROOT/rtl/common/filelists/arbiter_round_robin.f
-f $REPO_ROOT/rtl/common/filelists/arbiter_single_client.f

# Package files
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# AXI write engine module
$STREAM_ROOT/rtl/fub/axi_write_engine.sv
