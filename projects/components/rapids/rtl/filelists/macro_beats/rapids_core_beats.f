# RAPIDS Core Beats Macro File List
# Location: projects/components/rapids/rtl/filelists/macro_beats/rapids_core_beats.f
# Purpose: Complete RAPIDS Beats Core (Scheduler Array + Sink Path + Source Path)

# Include scheduler group array dependencies
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/macro_beats/scheduler_group_array_beats.f

# Include sink data path dependencies
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/macro_beats/snk_data_path_beats.f

# Include source data path dependencies
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/macro_beats/src_data_path_beats.f

# Includes
+incdir+$REPO_ROOT/projects/components/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# DUT module
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/rapids_core_beats.sv
