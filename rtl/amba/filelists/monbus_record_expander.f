# Filelist for monbus_record_expander
# Location: rtl/amba/filelists/monbus_record_expander.f
#
# The raw 3-beat record expander lifted out of monbus_group_core (2026-10-23)
# so monbus_group_core_1wr can run one per source.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f
$REPO_ROOT/rtl/amba/ocelus/monbus_record_expander.sv
