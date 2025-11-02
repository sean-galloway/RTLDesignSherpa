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

# Package files (MUST be first)
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$REPO_ROOT/projects/components/rapids/rtl/includes/rapids_pkg.sv

# Main module
$REPO_ROOT/projects/components/rapids/rtl/rapids_fub/ctrlrd_engine.sv

# Dependencies
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
