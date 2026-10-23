# rapids-g (rapids TASK-034): macro/rapids_core.f with both halves and the array swapped
# for their generated _g modules.
# RAPIDS Core Beats Macro File List
# Location: projects/components/dma-ip/rapids/rtl/filelists/macro_g/rapids_core_g.f
# Purpose: Complete RAPIDS Beats Core - thin wrapper over the two independent
#          half cores (rapids_src + rapids_snk).
#
# Dedup note: both half filelists (rapids_src.f / rapids_snk.f) each
# pull scheduler_group_array.f, so they cannot both be included here (that
# would define the scheduler-array sources twice). Instead the shared scheduler
# array is included ONCE, alongside each half's data-path filelist, then the two
# half module .sv files, and finally the wrapper DUT. Every RTL source appears
# exactly once.

# Shared scheduler group array dependencies (included ONCE for both halves)
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro_g/scheduler_group_array_g.f

# Sink data path dependencies (AXIS-fronted; tid = channel)
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro/snk_data_path_axis.f

# Source data path dependencies (AXIS-fronted; tid = channel)
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro/src_data_path_axis.f

# AXIS monitor-lite wrappers on each half's network port (rapids TASK-015); the
# loader dedups, so the shared axis_monitor_lite.f pulled by both is compiled once
-f $REPO_ROOT/rtl/amba/filelists/axis4_slave_monlite.f
-f $REPO_ROOT/rtl/amba/filelists/axis4_master_monlite.f

# Includes
+incdir+$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Half module cores (instantiated by the wrapper DUT)
# Tile header decode in the sink half (TILE_HDR); deps already above
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/fub/rapids_tile_hdr_rx.sv
# End-to-end tile credits in the source half (TILE_CREDITS); deps already above
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/fub/rapids_tile_credits.sv
# Straps toward RAPIDS (TILE_CREDITS): landing space, intake queue, credit returns
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/fub/rapids_tile_landing.sv
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/fub/rapids_tile_desc_intake.sv
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/fub/rapids_tile_credit_tx.sv
# Stalled-data check on MonBus (TILE_CREDITS)
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/fub/rapids_tile_stall_mon.sv
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/macro_g/generated/rapids_snk_g.sv
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/macro_g/generated/rapids_src_g.sv

# DUT module (thin wrapper)
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/macro_g/generated/rapids_core_g.sv
