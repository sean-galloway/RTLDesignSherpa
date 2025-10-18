# RAPIDS Scheduler Group Array Macro File List
# Location: projects/components/rapids/rtl/filelists/macro/scheduler_group_array.f
# Purpose: Scheduler Group Array (32x instantiation of scheduler_group)

# Include scheduler_group file list (pulls in FUBs, packages, all dependencies)
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/macro/scheduler_group.f

# Additional AXI Monitor infrastructure (needed by axi4_master_*_mon in scheduler_group_array)
# Counter dependencies (needed by axi_monitor_timer)
$REPO_ROOT/rtl/common/counter_load_clear.sv
$REPO_ROOT/rtl/common/counter_freq_invariant.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_trans_mgr.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_timer.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_timeout.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_reporter.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_base.sv
$REPO_ROOT/rtl/amba/shared/axi_monitor_filtered.sv

# AXI4 Master Monitor modules (base + clock gating versions)
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd_mon.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr_mon.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd_mon_cg.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr_mon_cg.sv

# DUT module
$REPO_ROOT/projects/components/rapids/rtl/rapids_macro/scheduler_group_array.sv
