# Filelist for bridge_wr_rate_buf
# Location: projects/components/fabric-gen-ip/bridge/rtl/filelists_static/bridge_wr_rate_buf.f
#
# Hand-written bridge IP (see bridge_cam.f for why this directory exists): the
# write rate-matching buffer the generator instantiates on a master's upsized
# path into a shared slave. Proof: formal/bridge/bridge_wr_rate_buf/.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f

$BRIDGE_ROOT/rtl/bridge_wr_rate_buf.sv
