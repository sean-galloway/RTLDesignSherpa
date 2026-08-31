# Filelist for axi_monitor_base
# Location: rtl/amba/filelists/axi_monitor_base.f
#
# Generated from the inline verilog_sources lists in val/amba.
# Compile order is significant and preserved from the original tests.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba4_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba5_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_arbiter_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/counter_load_clear.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
-f $REPO_ROOT/rtl/common/filelists/counter_freq_invariant.f
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/monitor/monitor_trans_cam.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_trans_mgr.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_timer.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_timeout.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter_error.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter_timeout.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter_compl.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter_threshold.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter_perf.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter_debug.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_reporter.sv
# axi_monitor_base instantiates axi_monitor_addr_check under
# `if (N_ADDR_RANGES > 0)`. A generate-gated submodule is INVISIBLE to
# default-parameter elaboration, so this list looked complete while the
# default build (N_ADDR_RANGES=0) was the only one anyone built from it --
# and any consumer setting N_ADDR_RANGES>0 failed with "Cannot find file
# containing module: 'axi_monitor_addr_check'". Listed here so the filelist
# covers the module's configurations, not just its default one.
$REPO_ROOT/rtl/amba/monitor/axi_monitor_addr_check.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_base.sv
