# Filelist for wb4_master_slave_loop (test collateral: master <-> slave loop)
# Location: rtl/amba/filelists/wb4_master_slave_loop.f

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/wb4_master.f
$REPO_ROOT/rtl/amba/wb4/wb4_slave.sv
$REPO_ROOT/rtl/amba/testcode/wb4_master_slave_loop.sv
