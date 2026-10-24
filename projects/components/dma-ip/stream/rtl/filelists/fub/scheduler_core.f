# Filelist for scheduler_core (the STREAM scheduler datapath, stream TASK-020)
# Location: projects/components/dma-ip/stream/rtl/filelists/fub/scheduler_core.f
#
# Shared by the FSM scheduler (scheduler.f) and the gatling-sequenced
# scheduler_g (fub_g). The run-base generators are the WRAPPERS' (scheduler
# instantiates stream_run_addr_gen; scheduler_g fills FIFOs from firmware), so
# they are not here.

# Include directories
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Each filelist declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f

# Package files
$STREAM_ROOT/rtl/includes/stream_pkg.sv

# The datapath
$STREAM_ROOT/rtl/fub/scheduler_core.sv
