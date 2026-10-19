# Filelist for bridge_cdc_slave_arb
# Location: projects/components/fabric-gen-ip/bridge/rtl/filelists_static/bridge_cdc_slave_arb.f
#
# Hand-written bridge RTL (not generated): slave-domain arbitration for a
# multi-master slave on its own clock (bridge W9). Instantiated by the slave
# adapter of every cdc = true slave that two or more masters reach.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
-f $REPO_ROOT/rtl/cdc/filelists/gaxi_fifo_async.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/rtl/common/filelists/arbiter_matrix.f

$BRIDGE_ROOT/rtl/bridge_cdc_slave_arb.sv
