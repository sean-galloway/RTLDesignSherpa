# RAPIDS Ctrlwr Engine FUB File List
# Location: projects/components/rapids/rtl/filelists/fub/ctrlwr_engine.f
# Purpose: Ctrlwr Engine module and its direct dependencies

# Include directories
+incdir+$REPO_ROOT/projects/components/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/rtl/common/includes

# Package files (MUST be first, in dependency order)
$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba4_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba5_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_arbiter_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$REPO_ROOT/projects/components/rapids/rtl/includes/rapids_pkg.sv

# Dependencies
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# DUT module
$REPO_ROOT/projects/components/rapids/rtl/fub/ctrlwr_engine.sv
