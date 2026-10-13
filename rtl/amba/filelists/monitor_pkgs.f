# Filelist for monitor_pkgs
# Location: rtl/amba/filelists/monitor_pkgs.f
#
# Declares the complete compile closure for this component: packages,
# rtl/common dependencies and sub-blocks. Consumers -f include this file
# rather than hand-listing its contents, so internal changes stay internal.

+incdir+$REPO_ROOT/rtl/amba/includes

# Ocelus type packages only - no modules. For consumers whose port lists
# reference monitor_common_pkg::monitor_packet_t and friends by name but
# that do not instantiate a ocelus.
$REPO_ROOT/rtl/amba/includes/ocelus_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/ocelus_amba4_pkg.sv
$REPO_ROOT/rtl/amba/includes/ocelus_amba5_pkg.sv
$REPO_ROOT/rtl/amba/includes/ocelus_arbiter_pkg.sv
$REPO_ROOT/rtl/amba/includes/ocelus_pkg.sv
