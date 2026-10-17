# RAPIDS Shared Descriptor Engine FUB File List
# Location: projects/components/dma-ip/rapids/rtl/filelists/fub/descriptor_engine_shared.f
# Purpose: descriptor_engine_shared (one fetch engine for every channel of a half)

+incdir+$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f

$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes/rapids_pkg.sv

# DUT module
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/fub/descriptor_engine_shared.sv
