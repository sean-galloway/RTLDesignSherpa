# RAPIDS Source Beats Macro File List
# Location: projects/components/dmas/rapids/rtl/filelists/macro_beats/rapids_src_beats.f
# Purpose: Source-only RAPIDS Beats (Scheduler Array [read-only] + Source Path)

# Include scheduler group array dependencies
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/macro_beats/scheduler_group_array_beats.f

# Include source data path dependencies (AXIS-fronted; tid = channel)
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/macro_beats/src_data_path_axis_beats.f

# Includes
+incdir+$REPO_ROOT/projects/components/dmas/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# DUT module
$REPO_ROOT/projects/components/dmas/rapids/rtl/macro_beats/rapids_src_beats.sv
