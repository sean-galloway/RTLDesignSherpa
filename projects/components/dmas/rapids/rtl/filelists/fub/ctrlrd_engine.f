# RAPIDS Control Read Engine (ctrlrd_engine) RTL Filelist
# Location: projects/components/dmas/rapids/rtl/filelists/fub/ctrlrd_engine.f
# Purpose: Pre-descriptor control read engine with retry mechanism
#
# Dependencies:
# - monitor_pkg.sv (monitor event definitions)
# - rapids_pkg.sv (RAPIDS-specific definitions)
# - gaxi_skid_buffer.sv (2-deep skid buffer for request buffering)

# Include directories
+incdir+$REPO_ROOT/projects/components/dmas/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/rtl/common/includes

# Package files (MUST be first, in dependency order)
# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f

$REPO_ROOT/projects/components/dmas/rapids/rtl/includes/rapids_pkg.sv

# DUT module
$REPO_ROOT/projects/components/dmas/rapids/rtl/fub/ctrlrd_engine.sv
