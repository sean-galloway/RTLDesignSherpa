# RAPIDS Ctrlwr Engine FUB File List
# Location: projects/components/rapids/rtl/filelists/fub/ctrlwr_engine.f
# Purpose: Ctrlwr Engine module and its direct dependencies

# Include directories
+incdir+$REPO_ROOT/projects/components/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/rtl/common/includes

# Package files (MUST be first)
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$REPO_ROOT/projects/components/rapids/rtl/includes/rapids_pkg.sv

# Dependencies
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# DUT module
$REPO_ROOT/projects/components/rapids/rtl/rapids_fub/ctrlwr_engine.sv
