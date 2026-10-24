# Filelist for monbus_axi4_group_1wr
# Location: rtl/amba/filelists/monbus_axi4_group_1wr.f
#
# AXI4 burst master-write wrapper for the single-write-port group core
# (2026-10-23). No slave-read side.

-f $REPO_ROOT/rtl/amba/filelists/monbus_group_core_1wr.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_wr.f
$REPO_ROOT/rtl/amba/ocelus/monbus_axi4_group_1wr.sv
