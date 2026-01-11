# RAPIDS Beats Scheduler Group Array Macro File List
# Location: projects/components/rapids/rtl/filelists/macro_beats/scheduler_group_array_beats.f
# Purpose: Array of beats_scheduler_group modules with shared resources

# Include beats_scheduler_group which pulls in all FUB dependencies
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/macro_beats/scheduler_group_beats.f

# Additional common RTL dependencies (not in axi4_master_rd_mon.f)
-f $REPO_ROOT/rtl/common/filelists/counter_freq_invariant.f

# AXI4 Master Read Monitor and all its dependencies
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd_mon.f

# DUT module
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/scheduler_group_array_beats.sv
