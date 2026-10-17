# STREAM shared descriptor engine (one fetch engine for every channel)
# Location: projects/components/dma-ip/stream/rtl/filelists/fub/descriptor_engine_shared.f
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f
$STREAM_ROOT/rtl/includes/stream_pkg.sv
$STREAM_ROOT/rtl/fub/descriptor_engine_shared.sv
