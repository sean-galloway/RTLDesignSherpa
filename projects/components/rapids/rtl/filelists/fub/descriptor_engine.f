# RAPIDS Descriptor Engine FUB File List
# Location: projects/components/rapids/rtl/filelists/fub/descriptor_engine.f
# Purpose: Descriptor Engine module and its direct dependencies

# Include directories
+incdir+$REPO_ROOT/projects/components/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/rtl/common/includes

# Package files (MUST be first)
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$REPO_ROOT/projects/components/rapids/rtl/includes/rapids_pkg.sv

# Dependencies
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/common/fifo_sync.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/common/counter_bin.sv

# DUT module
$REPO_ROOT/projects/components/rapids/rtl/rapids_fub/descriptor_engine.sv
