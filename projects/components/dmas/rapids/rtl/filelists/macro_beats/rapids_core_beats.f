# RAPIDS Core Beats Macro File List
# Location: projects/components/dmas/rapids/rtl/filelists/macro_beats/rapids_core_beats.f
# Purpose: Complete RAPIDS Beats Core - thin wrapper over the two independent
#          half cores (rapids_src_beats + rapids_snk_beats).
#
# Dedup note: both half filelists (rapids_src_beats.f / rapids_snk_beats.f) each
# pull scheduler_group_array_beats.f, so they cannot both be included here (that
# would define the scheduler-array sources twice). Instead the shared scheduler
# array is included ONCE, alongside each half's data-path filelist, then the two
# half module .sv files, and finally the wrapper DUT. Every RTL source appears
# exactly once.

# Shared scheduler group array dependencies (included ONCE for both halves)
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/macro_beats/scheduler_group_array_beats.f

# Sink data path dependencies (AXIS-fronted; tid = channel)
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/macro_beats/snk_data_path_axis_beats.f

# Source data path dependencies (AXIS-fronted; tid = channel)
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/macro_beats/src_data_path_axis_beats.f

# Includes
+incdir+$REPO_ROOT/projects/components/dmas/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Half module cores (instantiated by the wrapper DUT)
$REPO_ROOT/projects/components/dmas/rapids/rtl/macro_beats/rapids_snk_beats.sv
$REPO_ROOT/projects/components/dmas/rapids/rtl/macro_beats/rapids_src_beats.sv

# DUT module (thin wrapper)
$REPO_ROOT/projects/components/dmas/rapids/rtl/macro_beats/rapids_core_beats.sv
