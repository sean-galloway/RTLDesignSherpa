# RAPIDS-g scheduler (rapids TASK-034): scheduler_core sequenced by firmware
# Location: projects/components/dma-ip/rapids/rtl/filelists/fub_g/scheduler_g.f
# The run-base generators are firmware here, so stream_run_addr_gen is not
# in the closure (the FSM scheduler's filelist, fub/scheduler.f, has it).

+incdir+$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f
# descriptor skid (TASK-028 / TASK-017)
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f

$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes/rapids_pkg.sv

$REPO_ROOT/projects/components/dma-ip/rapids/rtl/fub/scheduler_core.sv
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/fub_g/scheduler_g_base_fifo.sv
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/fub_g/scheduler_g.sv
