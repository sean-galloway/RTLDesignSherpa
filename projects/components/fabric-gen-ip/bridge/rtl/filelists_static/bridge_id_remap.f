# Filelist for bridge_id_remap
# Location: projects/components/fabric-gen-ip/bridge/rtl/filelists_static/bridge_id_remap.f
#
# Hand-written bridge IP (see bridge_cam.f for why this directory exists): the
# per-master transaction-ID remap table the generator instantiates in a master
# adapter whose ID is wider than its outstanding-slot index.
# Proof: formal/bridge/bridge_id_remap/.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

$BRIDGE_ROOT/rtl/bridge_id_remap.sv
