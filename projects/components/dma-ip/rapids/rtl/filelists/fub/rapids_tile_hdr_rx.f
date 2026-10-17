# Filelist for rapids_tile_hdr_rx
# Location: projects/components/dma-ip/rapids/rtl/filelists/fub/rapids_tile_hdr_rx.f
# Purpose: Sink-port tile header decode (TILE_SPEC 11.5 / 11.11)

+incdir+$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f

$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes/rapids_pkg.sv

# DUT module
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/fub/rapids_tile_hdr_rx.sv
