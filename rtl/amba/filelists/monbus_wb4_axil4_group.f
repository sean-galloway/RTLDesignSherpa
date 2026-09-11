# Filelist for monbus_wb4_axil4_group
# Location: rtl/amba/filelists/monbus_wb4_axil4_group.f
# Purpose: monbus_axil4_axil4_group with a Wishbone B4 read port in place of the AXI4-Lite one

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/monbus_axil4_axil4_group.f
-f $REPO_ROOT/rtl/amba/filelists/wb4_slave.f
$REPO_ROOT/rtl/amba/monitor/monbus_wb4_rd_shim.sv
$REPO_ROOT/rtl/amba/monitor/monbus_wb4_axil4_group.sv
