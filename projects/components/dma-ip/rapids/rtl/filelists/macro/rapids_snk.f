# RAPIDS Sink Beats Macro File List
# Location: projects/components/dma-ip/rapids/rtl/filelists/macro/rapids_snk.f
# Purpose: Write-Only RAPIDS Beats Sink Core (Scheduler Array + Sink Path)

# Include scheduler group array dependencies
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro/scheduler_group_array.f

# Include sink data path dependencies (AXIS-fronted; tid = channel)
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro/snk_data_path_axis.f

# Sink-ingress AXIS monitor-lite wrapper (axis4_slave skid + axis_monitor_lite tap), rapids TASK-015
# plane_mon_* port types; the network endpoint itself is in rtl/plane (filelists/plane)
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f

# Includes
+incdir+$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# DUT module
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/macro/rapids_snk.sv
