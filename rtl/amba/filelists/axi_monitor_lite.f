# Filelist for axi_monitor_lite (rtl/amba/ocelus/axi_monitor_lite.sv)
# Location: rtl/amba/filelists/axi_monitor_lite.f
#
# The lite ocelus and everything it needs: the ocelus packages (packet
# format, event codes) and the frequency-invariant tick counter. Its output
# queue is a gaxi_fifo_sync (unreset storage, mux read). The optional
# address-range checker is the full ocelus's axi_monitor_addr_check.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/ocelus_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/ocelus_amba4_pkg.sv
-f $REPO_ROOT/rtl/common/filelists/counter_freq_invariant.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_addr_check.sv
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_lite.sv
