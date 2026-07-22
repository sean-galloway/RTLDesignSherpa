# Filelist for axi_read_engine module
# Location: projects/components/dmas/stream/rtl/filelists/fub/axi_read_engine.f

# Include directories
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f
-f $REPO_ROOT/rtl/common/filelists/arbiter_round_robin.f
-f $REPO_ROOT/rtl/common/filelists/arbiter_single_client.f

-f $REPO_ROOT/rtl/amba/filelists/fifo_defs.f

# Package files
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# AXI read engine module
$STREAM_ROOT/rtl/fub/axi_read_engine.sv
