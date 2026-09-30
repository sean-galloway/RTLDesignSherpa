# RAPIDS Source Data Path AXIS Test Wrapper File List
# Location: projects/components/dma-ip/rapids/rtl/filelists/macro/src_data_path_axis_test.f
# Purpose: Test wrapper with 8 schedulers + source_data_path_axis for realistic testing

# Include scheduler dependencies (packages, etc.)
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/fub/scheduler.f

# Include source_data_path_axis dependencies
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro/src_data_path_axis.f

# DUT module (test wrapper)
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/macro/src_data_path_axis_test.sv
