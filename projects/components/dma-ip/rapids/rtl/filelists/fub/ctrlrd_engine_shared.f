# RAPIDS Shared Control-Read Engine FUB File List
# Location: projects/components/dma-ip/rapids/rtl/filelists/fub/ctrlrd_engine_shared.f
# Purpose: ctrlrd_engine_shared (one ctrlrd_engine + scheduler-side arbitration)

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/fub/ctrlrd_engine.f

# DUT module
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/fub/ctrlrd_engine_shared.sv
