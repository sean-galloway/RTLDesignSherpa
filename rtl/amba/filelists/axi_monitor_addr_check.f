# Filelist for axi_monitor_addr_check
# Location: rtl/amba/filelists/axi_monitor_addr_check.f
#
# The module is pulled in as a dependency by axi_monitor_base.f; this
# standalone list exists so it can be elaborated on its own, which is what the
# directed payload-stability test does.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba4_pkg.sv
$REPO_ROOT/rtl/amba/monitor/axi_monitor_addr_check.sv
