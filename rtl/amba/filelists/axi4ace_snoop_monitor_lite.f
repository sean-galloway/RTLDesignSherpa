# Filelist for axi4ace_snoop_monitor_lite
# Location: rtl/amba/filelists/axi4ace_snoop_monitor_lite.f
#
# The ACE snoop lite ocelus and everything it needs: ocelus packages,
# the frequency-invariant tick counter, and the ocelus core.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/ocelus_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/ocelus_amba4_pkg.sv
-f $REPO_ROOT/rtl/common/filelists/counter_freq_invariant.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
$REPO_ROOT/rtl/amba/ocelus/axi4ace_snoop_monitor_lite.sv
