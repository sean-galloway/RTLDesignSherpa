# Filelist for axis_monitor_lite (rtl/amba/ocelus/axis_monitor_lite.sv)
# Location: rtl/amba/filelists/axis_monitor_lite.f
#
# The AXI4-Stream lite ocelus and everything it needs: the ocelus packages
# (packet format, AXIS event codes) and the frequency-invariant tick counter.
# Its output queue is inline (an unreset array), so no gaxi buffer is needed.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/ocelus_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/ocelus_amba4_pkg.sv
-f $REPO_ROOT/rtl/common/filelists/counter_freq_invariant.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
$REPO_ROOT/rtl/amba/ocelus/axis_monitor_lite.sv
