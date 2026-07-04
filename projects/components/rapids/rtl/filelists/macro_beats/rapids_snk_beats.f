# RAPIDS Sink Beats Macro File List
# Location: projects/components/rapids/rtl/filelists/macro_beats/rapids_snk_beats.f
# Purpose: Write-Only RAPIDS Beats Sink Core (Scheduler Array + Sink Path)

# Include scheduler group array dependencies
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/macro_beats/scheduler_group_array_beats.f

# Include sink data path dependencies (AXIS-fronted; tid = channel)
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/macro_beats/snk_data_path_axis_beats.f

# Includes
+incdir+$REPO_ROOT/projects/components/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# DUT module
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/rapids_snk_beats.sv
