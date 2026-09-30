# RAPIDS Sink Data Path AXIS Test Wrapper File List
# Location: projects/components/dma-ip/rapids/rtl/filelists/macro/snk_data_path_axis_test.f
# Purpose: Test wrapper with 8 schedulers + sink_data_path_axis for realistic testing

# Include scheduler dependencies (packages, etc.)
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/fub/scheduler.f

# Include sink_data_path_axis dependencies
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro/snk_data_path_axis.f

# DUT module (test wrapper)
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/macro/snk_data_path_axis_test.sv
