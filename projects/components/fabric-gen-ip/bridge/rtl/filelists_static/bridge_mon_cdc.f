# Filelist for bridge_mon_cdc
# Location: projects/components/fabric-gen-ip/bridge/rtl/filelists_static/bridge_mon_cdc.f
#
# Hand-written bridge RTL (not generated): carries an Ocelus port monitor that
# runs on a slave's own clock into the aclk monbus group. Instantiated by the
# slave adapter of a monitored cdc slave that two or more masters reach
# (bridge W9: its monitors sit on s_aclk, after bridge_cdc_slave_arb).

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f
-f $REPO_ROOT/rtl/cdc/filelists/gaxi_fifo_async.f
-f $REPO_ROOT/rtl/cdc/filelists/bin2gray.f
-f $REPO_ROOT/rtl/cdc/filelists/gray2bin.f
-f $REPO_ROOT/rtl/cdc/filelists/glitch_free_n_dff_arn.f

$BRIDGE_ROOT/rtl/bridge_mon_cdc.sv
