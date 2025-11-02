# RAPIDS Scheduler FUB File List
# Location: projects/components/rapids/rtl/filelists/fub/scheduler.f
# Purpose: Scheduler module and its direct dependencies

# Include directories
+incdir+$REPO_ROOT/projects/components/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Package files (MUST be first)
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$REPO_ROOT/projects/components/rapids/rtl/includes/rapids_pkg.sv

# DUT module
$REPO_ROOT/projects/components/rapids/rtl/rapids_fub/scheduler.sv
