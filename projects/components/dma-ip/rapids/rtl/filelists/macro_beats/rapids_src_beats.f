# RAPIDS Source Beats Macro File List
# Location: projects/components/dma-ip/rapids/rtl/filelists/macro_beats/rapids_src_beats.f
# Purpose: Source-only RAPIDS Beats (Scheduler Array [read-only] + Source Path)

# Include scheduler group array dependencies
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro_beats/scheduler_group_array_beats.f

# Include source data path dependencies (AXIS-fronted; tid = channel)
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro_beats/src_data_path_axis_beats.f

# Source-egress AXIS monitor-lite wrapper (axis4_master skid + axis_monitor_lite tap), rapids TASK-015
-f $REPO_ROOT/rtl/amba/filelists/axis4_master_monlite.f

# Includes
+incdir+$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# DUT module
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/macro_beats/rapids_src_beats.sv
