# RAPIDS Beats Scheduler Group Array Macro File List
# Location: projects/components/dma-ip/rapids/rtl/filelists/macro/scheduler_group_array.f
# Purpose: Array of scheduler_group modules with shared resources

# Include scheduler_group which pulls in all FUB dependencies
# reset_defs.svh -- this module uses `ALWAYS_FF_RST, so its macro header
# must be on the include path and compiled before it.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro/scheduler_group.f

# Additional common RTL dependencies (not in axi4_master_rd_mon.f)
-f $REPO_ROOT/rtl/common/filelists/counter_freq_invariant.f

# AXI4 Master Read Monitor and all its dependencies
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd_monlite.f

# Descriptor-AXI perf window meter (DAXMON_PERF_* buckets), the same meter the top uses for RDMON/WRMON
-f $REPO_ROOT/rtl/amba/filelists/axi_bus_meter.f

# DUT module
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/macro/scheduler_group_array.sv
