# Filelist for wb4_slave_cdc
# Location: rtl/amba/filelists/wb4_slave_cdc.f

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/fifo_defs.svh
-f $REPO_ROOT/rtl/amba/filelists/wb4_slave.f
-f $REPO_ROOT/rtl/cdc/filelists/gaxi_fifo_async.f
$REPO_ROOT/rtl/amba/wb4/wb4_slave_cdc.sv
