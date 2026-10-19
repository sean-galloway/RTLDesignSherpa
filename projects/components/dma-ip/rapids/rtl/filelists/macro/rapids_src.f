# RAPIDS Source Beats Macro File List
# Location: projects/components/dma-ip/rapids/rtl/filelists/macro/rapids_src.f
# Purpose: Source-only RAPIDS Beats (Scheduler Array [read-only] + Source Path)

# Include scheduler group array dependencies
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro/scheduler_group_array.f

# Include source data path dependencies (AXIS-fronted; tid = channel)
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro/src_data_path_axis.f

# Source-egress AXIS monitor-lite wrapper (axis4_master skid + axis_monitor_lite tap), rapids TASK-015
# plane_mon_* port types; the network endpoint itself is in rtl/plane (filelists/plane)
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f

# Includes
+incdir+$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# End-to-end tile credits in the source half (TILE_CREDITS); deps already above
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/fub/rapids_tile_credits.sv
# Stalled-data check on MonBus (TILE_CREDITS)
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/fub/rapids_tile_stall_mon.sv

# DUT module
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/macro/rapids_src.sv
