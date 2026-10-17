# RAPIDS Shared Control-Write Engine FUB File List
# Location: projects/components/dma-ip/rapids/rtl/filelists/fub/ctrlwr_engine_shared.f
# Purpose: ctrlwr_engine_shared (one ctrlwr_engine + scheduler-side arbitration)

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/fub/ctrlwr_engine.f

# DUT module
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/fub/ctrlwr_engine_shared.sv
