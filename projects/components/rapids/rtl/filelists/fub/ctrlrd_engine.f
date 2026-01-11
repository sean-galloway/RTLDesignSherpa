# RAPIDS Control Read Engine (ctrlrd_engine) RTL Filelist
# Location: projects/components/rapids/rtl/filelists/fub/ctrlrd_engine.f
# Purpose: Pre-descriptor control read engine with retry mechanism
#
# Dependencies:
# - monitor_pkg.sv (monitor event definitions)
# - rapids_pkg.sv (RAPIDS-specific definitions)
# - gaxi_skid_buffer.sv (2-deep skid buffer for request buffering)

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
$REPO_ROOT/projects/components/rapids/rtl/fub/ctrlrd_engine.sv
