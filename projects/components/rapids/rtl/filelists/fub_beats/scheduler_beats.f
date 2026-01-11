# RAPIDS Scheduler FUB File List (Beats-specific)
# Location: projects/components/rapids/rtl/filelists/fub_beats/scheduler_beats.f
# Purpose: Scheduler module and its direct dependencies (STREAM-based, beats mode)

# Include directories
+incdir+$REPO_ROOT/projects/components/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Package files (MUST be first, in dependency order)
$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba4_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_amba5_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_arbiter_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$REPO_ROOT/projects/components/rapids/rtl/includes/rapids_pkg.sv

# DUT module
$REPO_ROOT/projects/components/rapids/rtl/fub_beats/scheduler_beats.sv
