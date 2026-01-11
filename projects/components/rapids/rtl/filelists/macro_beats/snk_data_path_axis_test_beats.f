# RAPIDS Sink Data Path AXIS Test Wrapper File List
# Location: projects/components/rapids/rtl/filelists/macro_beats/snk_data_path_axis_test_beats.f
# Purpose: Test wrapper with 8 schedulers + sink_data_path_axis for realistic testing

# Include scheduler dependencies (packages, etc.)
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/fub_beats/scheduler_beats.f

# Include sink_data_path_axis dependencies
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/macro_beats/snk_data_path_axis_beats.f

# DUT module (test wrapper)
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/snk_data_path_axis_test_beats.sv
