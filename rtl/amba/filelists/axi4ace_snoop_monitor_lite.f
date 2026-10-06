# Filelist for axi4ace_snoop_monitor_lite
# Location: rtl/amba/filelists/axi4ace_snoop_monitor_lite.f
#
# The ACE snoop lite monitor and everything it needs: monitor packages,
# the frequency-invariant tick counter, and the monitor core.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba4_pkg.sv
-f $REPO_ROOT/rtl/common/filelists/counter_freq_invariant.f
$REPO_ROOT/rtl/amba/monitor/axi4ace_snoop_monitor_lite.sv
