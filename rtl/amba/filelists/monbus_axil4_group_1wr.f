# Filelist for monbus_axil4_group_1wr
# Location: rtl/amba/filelists/monbus_axil4_group_1wr.f
#
# AXIL single-beat master-write wrapper for the single-write-port group
# core (2026-10-23). No slave-read side.

-f $REPO_ROOT/rtl/amba/filelists/monbus_group_core_1wr.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_master_wr.f
$REPO_ROOT/rtl/amba/ocelus/monbus_axil4_group_1wr.sv
