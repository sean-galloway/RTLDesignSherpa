# Filelist for apb_monitor_addr_check
# Location: rtl/amba/filelists/apb_monitor_addr_check.f
#
# The module is pulled in as a dependency by apb4_monitor.f / apb5_monitor.f;
# this standalone list exists so it can be elaborated on its own -- which is
# what the directed payload-stability test does.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/ocelus_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/ocelus_amba4_pkg.sv
$REPO_ROOT/rtl/amba/ocelus/apb_monitor_addr_check.sv
