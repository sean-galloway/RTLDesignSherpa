# Filelist for axis_monitor_lite (rtl/amba/monitor/axis_monitor_lite.sv)
# Location: rtl/amba/filelists/axis_monitor_lite.f
#
# The AXI4-Stream lite monitor and everything it needs: the monitor packages
# (packet format, AXIS event codes) and the frequency-invariant tick counter.
# Its output queue is inline (an unreset array), so no gaxi buffer is needed.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba4_pkg.sv
-f $REPO_ROOT/rtl/common/filelists/counter_freq_invariant.f
$REPO_ROOT/rtl/amba/monitor/axis_monitor_lite.sv
